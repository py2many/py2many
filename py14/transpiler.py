import ast
import sys

from .clike import CLikeTranspiler
from .tracer import decltype

from py2many.context import add_variable_context, add_list_calls
from py2many.inference import InferMeta
from py2many.scope import add_scope_context
from py2many.analysis import add_imports, is_void_function, get_id
from py2many.tracer import is_list, is_builtin_import, defined_before


# TODO: merge this into py2many.cli.transpiler and fixup the tests
def transpile(source, headers=False, testing=False):
    """
    Transpile a single python translation unit (a python script) into
    C++ 14 code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    add_imports(tree)

    transpiler = CppTranspiler()

    buf = []
    if testing:
        buf += ['#include "catch.hpp"']
        transpiler.use_catch_test_cases = True

    if headers:
        buf += transpiler._headers
        buf += transpiler._usings

    if testing or headers:
        buf.append("")  # Force empty line

    cpp = transpiler.visit(tree)
    return "\n".join(buf) + cpp


def generate_catch_test_case(node, body):
    funcdef = 'TEST_CASE("{0}")'.format(node.name)
    return funcdef + " {\n" + body + "\n}"


def generate_template_fun(node, body):
    params = []
    for idx, arg in enumerate(node.args.args):
        params.append(("T" + str(idx + 1), get_id(arg)))
    typenames = ["typename " + arg[0] for arg in params]

    template = "inline "
    if len(typenames) > 0:
        template = "template <{0}>\n".format(", ".join(typenames))
    params = ["{0} {1}".format(arg[0], arg[1]) for arg in params]

    return_type = "auto"
    if is_void_function(node):
        return_type = "void"

    if node.name == "main":
        template = ""
        return_type = "int"

    funcdef = "{0}{1} {2}({3})".format(
        template, return_type, node.name, ", ".join(params)
    )
    return funcdef + " {\n" + body + "\n}"


def generate_lambda_fun(node, body):
    params = ["auto {0}".format(param.id) for param in node.args.args]
    funcdef = "auto {0} = []({1})".format(node.name, ", ".join(params))
    return funcdef + " {\n" + body + "\n};"


class CppRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        return f"__tmp{self._temp}"

    def visit_Compare(self, node):
        left = self.visit(node.left)
        ops = [self.visit(op) for op in node.ops]
        comparators = [self.visit(cmp) for cmp in node.comparators]
        right = comparators[0]
        if isinstance(right, ast.List):
            tmp = ast.Name(id=self._get_temp(), lineno=node.lineno)
            comparators[0] = tmp
            return ast.If(
                test=ast.Constant(value=True),
                body=[
                    ast.Assign(targets=[tmp], value=right, lineno=node.lineno),
                    ast.Compare(left, ops, comparators, lineno=node.lineno),
                ],
                orelse=[],
                lineno=node.lineno,
            )

        return node


class CppTranspiler(CLikeTranspiler):

    CONTAINER_TYPES = {
        "List": "std::vector",
        "Dict": "std::map",
        "Set": "std::set",
        "Optional": "std::optional",
    }

    def __init__(self):
        super().__init__()
        # TODO: include only when needed
        self._headers = []
        self._usings = set([])
        self.use_catch_test_cases = False
        self._container_type_map = self.CONTAINER_TYPES

    def headers(self, meta: InferMeta):
        self._headers.append('#include "py14/runtime/sys.h"')
        self._headers.append('#include "py14/runtime/builtins.h"')
        if self.use_catch_test_cases:
            self._headers.append('#include "py14/runtime/catch.hpp"')
        if meta.has_fixed_width_ints:
            self._headers.append("#include <stdint.h>")
        return "\n".join(self._headers)

    def visit_FunctionDef(self, node):
        body = "\n".join([self.visit(n) for n in node.body])

        if (
            self.use_catch_test_cases
            and is_void_function(node)
            and node.name.startswith("test")
        ):
            return generate_catch_test_case(node, body)
        # is_void_function(node) or is_recursive(node):
        return generate_template_fun(node, body) + "\n"
        # else:
        #    return generate_lambda_fun(node, body)

    def visit_Attribute(self, node):
        attr = node.attr
        value_id = get_id(node.value)
        if is_builtin_import(value_id):
            return "py14::" + value_id + "::" + attr
        elif value_id == "math":
            if node.attr == "asin":
                return "std::asin"
            elif node.attr == "atan":
                return "std::atan"
            elif node.attr == "acos":
                return "std::acos"

        if is_list(node.value):
            if node.attr == "append":
                attr = "push_back"
        return value_id + "." + attr

    def visit_ClassDef(self, node):
        buf = [f"class {node.name} {{"]
        buf += [self.visit(b) for b in node.body]
        buf += ["}"]
        return "\n".join(buf) + "\n"

    def visit_Call(self, node):
        fname = self.visit(node.func)
        if node.args:
            args = [self.visit(a) for a in node.args]
            args = ", ".join(args)
        else:
            args = ""

        if fname == "int":
            return "py14::to_int({0})".format(args)
        elif fname == "str":
            return "std::to_string({0})".format(args)
        elif fname == "max":
            return "std::max({0})".format(args)
        elif fname == "range":
            self._headers.append('#include "py14/runtime/range.hpp"')
            if sys.version_info[0] >= 3:
                return "rangepp::xrange({0})".format(args)
            else:
                return "rangepp::range({0})".format(args)
        elif fname == "xrange":
            self._headers.append('#include "py14/runtime/range.hpp"')
            return "rangepp::xrange({0})".format(args)
        elif fname == "len":
            return "{0}.size()".format(self.visit(node.args[0]))
        elif fname == "print":
            buf = []
            self._headers.append("#include <iostream>")
            for n in node.args:
                value = self.visit(n)
                if isinstance(n, ast.List) or isinstance(n, ast.Tuple):
                    buf.append(
                        "std::cout << {0};".format(
                            " << ".join([self.visit(el) for el in n.elts])
                        )
                    )
                else:
                    buf.append("std::cout << {0};".format(value))
                buf.append('std::cout << " ";')
            return "\n".join(buf[:-1]) + "\nstd::cout << std::endl;"

        return "{0}({1})".format(fname, args)

    def visit_For(self, node):
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("for(auto {0} : {1}) {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Expr(self, node):
        s = self.visit(node.value)
        if s.strip() and not s.endswith(";"):
            s += ";"
        if s == ";":
            return ""
        else:
            return s

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "T"
        if node.annotation:
            typename = self.visit(node.annotation)
        return (typename, id)

    def visit_Lambda(self, node):
        _, args = self.visit(node.args)
        args_string = ", ".join([f"auto {a}" for a in args])
        body = self.visit(node.body)
        return f"[]({args_string}) {{ return {body}; }}"

    def visit_Str(self, node):
        """Use a C++ 14 string literal instead of raw string"""
        return "std::string {" + super().visit_Str(node) + "}"

    def visit_Name(self, node):
        if node.id == "None":
            return "nullptr"
        else:
            return super().visit_Name(node)

    def visit_Constant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif isinstance(node.value, str):
            return self.visit_Str(node)
        else:
            return super().visit_Constant(node)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        var_definitions = []
        for cv in node.common_vars:
            definition = node.scopes.find(cv)
            var_type = decltype(definition)
            var_definitions.append("{0} {1};\n".format(var_type, cv))

        if self.visit(node.test) == '__name__ == std::string {"__main__"}':
            buf = [
                "int main(int argc, char ** argv) {",
                "py14::sys::argv = " "std::vector<std::string>(argv, argv + argc);",
            ]
            buf.extend([self.visit(child) for child in node.body])
            buf.append("}")
            return "\n".join(buf)
        else:
            return "".join(var_definitions) + super().visit_If(node)

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super().visit_UnaryOp(node)

    def visit_BinOp(self, node):
        if (
            isinstance(node.left, ast.List)
            and isinstance(node.op, ast.Mult)
            and isinstance(node.right, ast.Num)
        ):
            return "std::vector ({0},{1})".format(
                self.visit(node.right), self.visit(node.left.elts[0])
            )
        else:
            return super().visit_BinOp(node)

    def visit_Module(self, node):
        buf = [self.visit(b) for b in node.body]
        return "\n".join(buf)

    def visit_alias(self, node):
        return '#include "{0}.h"'.format(node.name)

    def visit_Import(self, node):
        imports = [self.visit(n) for n in node.names]
        return "\n".join(i for i in imports if i)

    def visit_ImportFrom(self, node):
        if node.module in self.IGNORED_MODULE_LIST:
            return ""

        # TODO: use node.module below
        imports = [self.visit(n) for n in node.names]
        return "\n".join(i for i in imports if i)

    def visit_List(self, node):
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"{{{elements_str}}}"

    def visit_Subscript(self, node):
        value = self.visit(node.value)
        if isinstance(node.slice, ast.Ellipsis):
            raise NotImplementedError("Ellipsis not supported")

        slice_value = self._slice_value(node)
        index = self.visit(slice_value)
        if hasattr(node, "is_annotation"):
            if value in self.CONTAINER_TYPES:
                value = self.CONTAINER_TYPES[value]
            return "{0}<{1}>".format(value, index)
        return f"{value}[{index}]"

    def visit_Tuple(self, node):
        elts = [self.visit(e) for e in node.elts]
        return "std::make_tuple({0})".format(", ".join(elts))

    def visit_TryExcept(self, node, finallybody=None):
        self._headers.append("#include <iostream>")
        buf = ["try {"]
        buf += [self.visit(n) for n in node.body]
        buf.append("} catch (const std::exception& e) {")

        buf += [self.visit(h) for h in node.handlers]

        if finallybody:
            buf.append("try { // finally")
            buf += [self.visit(b) for b in finallybody]
            buf.append("} throw e;")

        buf.append("}")
        buf.append(
            "catch (const std::overflow_error& e) "
            '{ std::cout << "OVERFLOW ERROR" << std::endl; }'
        )
        buf.append(
            "catch (const std::runtime_error& e) "
            '{ std::cout << "RUNTIME ERROR" << std::endl; }'
        )
        buf.append("catch (...) " '{ std::cout << "UNKNOWN ERROR" << std::endl; 0}')

        return "\n".join(buf)

    def visit_Assert(self, node):
        if not self.use_catch_test_cases:
            self._headers.append("#include <cassert>")
            return "assert({0});".format(self.visit(node.test))
        return "REQUIRE({0});".format(self.visit(node.test))

    def visit_Assign(self, node):
        target = node.targets[0]

        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            value = self.visit(node.value)
            return "std::tie({0}) = {1};".format(", ".join(elts), value)

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            if target.id in outer_if.common_vars:
                value = self.visit(node.value)
                return "{0} = {1};".format(target.id, value)

        if isinstance(target, ast.Subscript):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)

        definition = node.scopes.find(target.id)
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            return "{0} {1} {{{2}}};".format(
                decltype(node), self.visit(target), ", ".join(elements)
            )
        else:
            typename = self._typename_from_annotation(target)
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{typename} {target} = {value};"

    def visit_AnnAssign(self, node):
        target, type_str, val = super().visit_AnnAssign(node)
        return f"{type_str} {target} = {val};"

    def visit_Print(self, node):
        buf = []
        for n in node.values:
            value = self.visit(n)
            if isinstance(n, ast.List) or isinstance(n, ast.Tuple):
                buf.append(
                    "std::cout << {0} << std::endl;".format(
                        " << ".join([self.visit(el) for el in n.elts])
                    )
                )
            else:
                buf.append("std::cout << {0} << std::endl;".format(value))
        return "\n".join(buf)
