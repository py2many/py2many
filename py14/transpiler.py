import ast
import functools
import textwrap

from .tracer import decltype
from .clike import CLikeTranspiler

from py2many.context import add_variable_context, add_list_calls
from py2many.declaration_extractor import DeclarationExtractor
from py2many.inference import InferMeta
from py2many.scope import add_scope_context
from py2many.analysis import add_imports, is_void_function, get_id
from py2many.rewriters import PythonMainRewriter
from py2many.tracer import (
    defined_before,
    is_builtin_import,
    is_class_or_module,
    is_enum,
    is_list,
    is_self_arg,
)

from typing import Optional, List, Tuple


# TODO: merge this into py2many.cli.transpiler and fixup the tests
def transpile(source, headers=False, testing=False):
    """
    Transpile a single python translation unit (a python script) into
    C++ 14 code.
    """
    tree = ast.parse(source)
    rewriter = PythonMainRewriter("cpp")
    tree = rewriter.visit(tree)
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


def generate_lambda_fun(node, body):
    params = ["auto {0}".format(param.id) for param in node.args.args]
    funcdef = "auto {0} = []({1})".format(node.name, ", ".join(params))
    return funcdef + " {\n" + body + "\n};"


class CppListComparisonRewriter(ast.NodeTransformer):
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
    NAME = "cpp"

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

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"#include {mod}" for mod in usings)
        return uses

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

        typenames, args = self.visit(node.args)

        args_list = []
        if len(args) and hasattr(node, "self_type"):
            # implicit this
            del typenames[0]
            del args[0]

        typedecls = []
        index = 0
        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]
            if typename == "T":
                typename = "T{0}".format(index)
                typedecls.append(typename)
                index += 1
            args_list.append(f"{typename} {arg}")

        template = "inline "
        if len(typedecls) > 0:
            typedecls_str = ", ".join([f"typename {t}" for t in typedecls])
            template = f"template <{typedecls_str}>"

        return_type = "auto"
        if node.name == "main":
            template = ""
            return_type = "int"

        if not is_void_function(node):
            if node.returns:
                typename = self._typename_from_annotation(node, attr="returns")
                return_type = f"{typename}"
            else:
                return_type = "auto"
        else:
            return_type = "void"

        args = ", ".join(args_list)
        funcdef = f"{template}{return_type} {node.name}({args}) {{"
        if getattr(node, "python_main", False):
            funcdef = "\n".join(
                [
                    "int main(int argc, char ** argv) {",
                    "py14::sys::argv = " "std::vector<std::string>(argv, argv + argc);",
                ]
            )
        return funcdef + "\n" + body + "}\n"

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

        if is_enum(value_id, node.scopes):
            return f"{value_id}::{attr}"

        if is_class_or_module(value_id, node.scopes):
            return f"{value_id}.{attr}"

        if is_self_arg(value_id, node.scopes):
            return f"this->{attr}"

        return f"{value_id}.{attr}"

    def visit_ClassDef(self, node):
        extractor = DeclarationExtractor(CppTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments

        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        buf = [f"class {node.name} {{"]
        buf += ["public:"]
        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            fields.append(f"{typename} {declaration}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        buf += [";\n".join(fields + [""])]
        body = [self.visit(b) for b in node.body]
        if node.is_dataclass:
            field_names = [arg for arg in declarations.keys()]
            args = ", ".join(fields)
            assignments = "; ".join(
                [f"this->{field} = {field}" for field in field_names]
            )
            constructor = f"{node.name}({args}) {{{assignments};}}"
            body = [constructor] + body
        buf += body
        buf += ["};"]
        return "\n".join(buf) + "\n"

    def _visit_enum(self, node, typename: str, fields: List[Tuple]):
        fields_list = []

        for field, value in fields:
            fields_list += [f"{field} = {value},"]
        fields_str = "".join(fields_list)
        return f"enum {node.name} : {typename} {{\n{fields_str}}};\n"

    def visit_IntEnum(self, node):
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = i
            fields.append((member, var))
        return self._visit_enum(node, "int", fields)

    def visit_IntFlag(self, node):
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = i
            fields.append((member, var))
        return self._visit_enum(node, "int", fields)

    def visit_StrEnum(self, node):
        fields = []
        definitions = []
        for i, (member, node_var) in enumerate(node.class_assignments.items()):
            var = self.visit(node_var)
            raw_string = node_var.raw_string
            if var == "auto()":
                var = f'"{member}"'
            fields.append(f"static const {node.name} {member};")
            definitions.append(
                f"const {node.name} {node.name}::{member}= {raw_string};"
            )
        fields = "\n".join([f for f in fields])
        definitions = "\n".join([d for d in definitions])
        return textwrap.dedent(
            f"""\
            class {node.name} : public std::string {{
            public:
              {node.name}(const char* s) : std::string(s) {{}}
              {fields}
            }};

            {definitions}

            """
        )

    def _dispatch(self, node, fname: str, vargs: List[str]) -> Optional[str]:
        def visit_range(node, vargs: List[str]) -> str:
            self._headers.append('#include "py14/runtime/range.hpp"')
            args = ", ".join(vargs)
            return f"rangepp::xrange({args})"

        def visit_print(node, vargs: List[str]) -> str:
            self._headers.append("#include <iostream>")
            buf = []
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

        dispatch_map = {
            "range": visit_range,
            "xrange": visit_range,
            "print": visit_print,
        }

        if fname in dispatch_map:
            return dispatch_map[fname](node, vargs)

        def visit_min_max(is_max: bool) -> str:
            min_max = "max" if is_max else "min"
            t1 = self._typename_from_annotation(node.args[0])
            t2 = None
            if len(node.args) > 1:
                t2 = self._typename_from_annotation(node.args[1])
            if hasattr(node.args[0], "container_type"):
                self._usings.add("<algorithm>")
                return f"*std::{min_max}_element({vargs[0]}.begin(), {vargs[0]}.end());"
            else:
                # C++ can't deal with max(1, size_t)
                if t1 == "int" and t2 == self._default_type:
                    vargs[0] = f"static_cast<size_t>({vargs[0]})"
                all_vargs = ", ".join(vargs)
                return f"std::{min_max}({all_vargs})"

        def visit_cast(cast_to: str) -> str:
            return f"static_cast<{cast_to}>({vargs[0]})"

        def visit_floor() -> str:
            self._headers.append("#include <math.h>")
            return f"static_cast<size_t>(floor({vargs[0]}))"

        # small one liners are inlined here as lambdas
        small_dispatch_map = {
            "int": lambda: f"py14::to_int({vargs[0]})",
            # Is py14::to_int() necessary?
            # "int": functools.partial(visit_cast, cast_to="i32"),
            "str": lambda: f"std::to_string({vargs[0]})",
            "len": lambda: f"{vargs[0]}.size()",
            "float": functools.partial(visit_cast, cast_to="float"),
            "max": functools.partial(visit_min_max, is_max=True),
            "min": functools.partial(visit_min_max, is_min=True),
            "floor": visit_floor,
            # "enumerate": lambda: f"{vargs[0]}.iter().enumerate()",
            # "sum": lambda: f"{vargs[0]}.iter().sum()",
            # # as usize below is a hack to pass comb_sort.rs. Need a better solution
            # "reversed": lambda: f"{vargs[0]}.iter().rev()",
            # "map": lambda: f"{vargs[1]}.iter().map({vargs[0]})",
            # "filter": lambda: f"{vargs[1]}.into_iter().filter({vargs[0]})",
            # "list": lambda: f"{vargs[0]}.collect::<Vec<_>>()",
        }

        if fname in small_dispatch_map:
            return small_dispatch_map[fname]()
        return None

    def visit_Call(self, node):
        fname = self.visit(node.func)
        vargs = []

        if node.args:
            vargs += [self.visit(a) for a in node.args]
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        ret = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret

        args = ", ".join(vargs)
        return f"{fname}({args})"

    def visit_For(self, node):
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("for(auto {0} : {1}) {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "T"
        if node.annotation:
            typename = self._typename_from_annotation(node)
        return (typename, id)

    def visit_Lambda(self, node):
        _, args = self.visit(node.args)
        args_string = ", ".join([f"auto {a}" for a in args])
        body = self.visit(node.body)
        return f"[]({args_string}) {{ return {body}; }}"

    def visit_Str(self, node):
        """Use a C++ 14 string literal instead of raw string"""
        node.raw_string = super().visit_Str(node)
        return f"std::string{{{node.raw_string}}}"

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

    def _make_block(self, node):
        buf = []
        buf.append("({")
        buf.extend([self.visit(child) for child in node.body])
        buf.append(";")
        buf.append("})")
        return "\n".join(buf)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        var_definitions = []
        for cv in node.common_vars:
            definition = node.scopes.find(cv)
            var_type = self._typename_from_annotation(definition)
            if var_type == self._default_type:
                var_type = decltype(definition)
            var_definitions.append("{0} {1};\n".format(var_type, cv))

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

    def _get_element_type(self, node):
        _ = self._typename_from_annotation(node)
        if hasattr(node, "container_type"):
            _, element_type = node.container_type
            return element_type
        else:
            return self._default_type

    def visit_List(self, node):
        self._headers.append("#include <vector>")
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        element_type = self._get_element_type(node)
        if element_type == self._default_type:
            typename = decltype(node)
            # Workaround for cases where we couldn't figure out type
            if "(None)" in typename:
                return f"{{{elements_str}}}"
            return f"{typename}{{{elements_str}}}"
        return f"std::vector<{element_type}>{{{elements_str}}}"

    def visit_Set(self, node):
        self._headers.append("#include <set>")
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        element_type = self._get_element_type(node)
        if element_type == self._default_type:
            typename = decltype(node)
            return f"{typename}{{{elements_str}}}"
        return f"std::set<{element_type}>{{{elements_str}}}"

    def visit_Dict(self, node):
        self._headers.append("#include <map>")
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(k) for k in node.values]
        kv_pairs = ", ".join([f"{{ {k}, {v} }}" for k, v in zip(keys, values)])
        _ = self._typename_from_annotation(node)
        if hasattr(node, "container_type"):
            container_type, element_type = node.container_type
            key_typename, value_typename = element_type
            if key_typename == self._default_type:
                key_typename = "int"
        else:
            typename = decltype(node)
            return f"{typename}{{{kv_pairs}}}"
        return f"std::map<{key_typename}, {value_typename}>{{{kv_pairs}}}"

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
        self._headers.append("#include <tuple>")
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

    def _visit_AssignOne(self, node, target):
        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            value = self.visit(node.value)
            return "std::tie({0}) = {1};".format(", ".join(elts), value)

        if isinstance(node.scopes[-1], ast.If) and isinstance(target, ast.Name):
            outer_if = node.scopes[-1]
            if target.id in outer_if.common_vars:
                value = self.visit(node.value)
                return "{0} = {1};".format(target.id, value)

        if isinstance(target, ast.Subscript):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)

        target_id = get_id(target)
        definition = node.scopes.find(target_id)
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            elements_str = ", ".join(elements)
            target = self.visit(target)
            element_typename = self._get_element_type(node.value)
            self._headers.append("#include <vector>")
            if element_typename == self._default_type:
                typename = decltype(node)
                return f"{typename} {target} = {{{elements_str}}};"
            return f"std::vector<{element_typename}> {target} = {{{elements_str}}};"
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
