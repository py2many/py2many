import ast
from typing import List

from py2many.analysis import get_id, is_void_function
from py2many.clike import class_for_typename
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import AstClassUsedBeforeDeclaration
from py2many.tracer import defined_before

from .clike import CLikeTranspiler
from .inference import get_inferred_mojo_type
from .plugins import (
    ATTR_DISPATCH_TABLE,
    CLASS_DISPATCH_TABLE,
    DECORATOR_DISPATCH_TABLE,
    DISPATCH_MAP,
    FUNC_DISPATCH_TABLE,
    FUNC_USINGS_MAP,
    MODULE_DISPATCH_TABLE,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)


class MojoTranspiler(CLikeTranspiler):
    NAME = "mojo"

    def __init__(self, indent=2):
        super().__init__()
        self._headers = set()
        self._indent = " " * indent
        CLikeTranspiler._default_type = "var"
        if "math" in self._ignored_module_set:
            self._ignored_module_set.remove("math")
        if "sys" in self._ignored_module_set:
            self._ignored_module_set.remove("sys")
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        self._func_usings_map = FUNC_USINGS_MAP

    def indent(self, code, level=1):
        return self._indent * level + code

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"import {mod}" for mod in usings)
        return uses

    @classmethod
    def _combine_value_index(cls, value_type, index_type) -> str:
        return f"{value_type}[{index_type}]"

    def comment(self, text):
        return f"# {text}\n"

    def visit_FunctionDef(self, node) -> str:
        body = "\n".join(
            [self.indent(self.visit(n), level=node.level + 1) for n in node.body]
        )
        typenames, args = self.visit(node.args)

        args_list = []
        if len(args) and hasattr(node, "self_type"):
            typenames[0] = node.self_type

        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]
            arg_node = node.args.args[i]
            # special case constructor self which mojo says should be passes as "inout"
            if node.name == "__init__" and arg == "self":
                arg = "inout " + arg
            elif getattr(arg_node, "owned", None):
                arg = "owned " + arg

            args_list.append(f"{arg}: {typename}")

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                typename = self._typename_from_annotation(node, attr="returns")
                return_type = f"{typename}"
            else:
                return_type = ""
        raises = " raises" if hasattr(node, "raises") else ""

        args = ", ".join(args_list)
        if return_type != "":
            funcdef = f"fn {node.name}({args}){raises} -> {return_type}:"
        else:
            funcdef = f"fn {node.name}({args}){raises}:"
        return self.indent(f"{funcdef}\n{body}\n", level=node.level)

    def visit_Return(self, node) -> str:
        if node.value:
            ret = self.visit(node.value)
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                return_type = self._typename_from_annotation(fndef, attr="returns")
                value_type = get_inferred_mojo_type(node.value)
                if getattr(node, "transfer", None):
                    # transfer sigil
                    ret = ret + "^"
                if return_type != value_type and value_type is not None:
                    return f"return {return_type}({ret})"
            return f"return {ret}"
        return "return"

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "T"
        if node.annotation:
            # This works only for arguments, for all other cases, use container_types
            typename = self._typename_from_annotation(node)
        return (typename, id)

    def visit_Lambda(self, node) -> str:
        # Not supported
        return "fn lambda(): pass"

    def visit_Attribute(self, node) -> str:
        attr = node.attr

        value_id = self.visit(node.value)

        if value_id == "sys":
            if attr == "argv":
                self._usings.add("os")
                return "(@[getAppFilename()] & commandLineParams())"

        if not value_id:
            value_id = ""

        ret = f"{value_id}.{attr}"
        if ret in self._attr_dispatch_table:
            ret = self._attr_dispatch_table[ret]
            return ret(self, node, value_id, attr)
        return ret

    def _visit_object_literal(self, node, fname: str, fndef: ast.ClassDef) -> str:
        vargs = []  # visited args
        if not hasattr(fndef, "declarations"):
            raise AstClassUsedBeforeDeclaration(fndef, node)
        if node.args:
            for arg, decl in zip(node.args, fndef.declarations.keys()):
                arg = self.visit(arg)
                vargs += [f"{decl}: {arg}"]
        if node.keywords:
            for kw in node.keywords:
                value = self.visit(kw.value)
                vargs += [f"{kw.arg}={value}"]
        args = ", ".join(vargs)
        return f"{fname}({args})"

    def visit_Call(self, node) -> str:
        fname = self.visit(node.func)
        fndef = node.scopes.find(fname)

        if isinstance(fndef, ast.ClassDef):
            return self._visit_object_literal(node, fname, fndef)

        vargs = []

        if node.args:
            vargs += [self.visit(a) for a in node.args]
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        ret = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret
        if vargs:
            args = ", ".join(vargs)
        else:
            args = ""
        return f"{fname}({args})"

    def visit_For(self, node) -> str:
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append(f"for {target} in {it}:")
        buf.extend(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        return "\n".join(buf)

    def visit_While(self, node) -> str:
        buf = []
        buf.append(f"while {self.visit(node.test)}:")
        buf.extend(
            [self.indent(self.visit(n), level=node.level + 1) for n in node.body]
        )
        return "\n".join(buf)

    def visit_Str(self, node) -> str:
        return "" + super().visit_Str(node) + ""

    def visit_Bytes(self, node) -> str:
        bytes_str = f"{node.s}"
        return bytes_str.replace("'", '"')  # replace single quote with double quote

    def visit_Name(self, node) -> str:
        if node.id == "None":
            return "nil"
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node) -> str:
        if node.value is None:
            return "nil"
        else:
            return super().visit_NameConstant(node)

    def visit_If(self, node) -> str:
        body_vars = {get_id(v) for v in node.scopes[-1].body_vars}
        orelse_vars = {get_id(v) for v in node.scopes[-1].orelse_vars}
        node.common_vars = body_vars.intersection(orelse_vars)

        body = "\n".join(
            [
                self.indent(self.visit(child), level=node.level + 1)
                for child in node.body
            ]
        )
        orelse = "\n".join(
            [
                self.indent(self.visit(child), level=node.level + 1)
                for child in node.orelse
            ]
        )
        test = self.visit(node.test)
        if node.orelse:
            orelse = self.indent(f"else:\n{orelse}", level=node.level)
        else:
            orelse = ""
        return f"if {test}:\n{body}\n{orelse}"

    def visit_UnaryOp(self, node) -> str:
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return f"-{self.visit(node.operand)}"
            else:
                return f"-({self.visit(node.operand)})"
        else:
            return super().visit_UnaryOp(node)

    def visit_ClassDef(self, node) -> str:
        extractor = DeclarationExtractor(MojoTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        decorators = [get_id(d) for d in node.decorator_list]
        for d in decorators:
            if d in CLASS_DISPATCH_TABLE:
                ret = CLASS_DISPATCH_TABLE[d](self, node)
                if ret is not None:
                    return ret

        decorators = [
            DECORATOR_DISPATCH_TABLE.get(d, lambda x, y: y)(self, node)
            for d in decorators
        ]
        mojo_decorators = "\n".join([f"@{d}" for d in decorators])
        if mojo_decorators != "":
            mojo_decorators = mojo_decorators + "\n"
        decorators = [
            class_for_typename(t, None, self._imported_names) for t in decorators
        ]

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = f"ST{index}"
                index += 1
            fields.append(f"var {declaration}: {typename}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        struct_def = f"{mojo_decorators}struct {node.name}:\n"
        struct_def += "\n".join([self.indent(f, level=node.level + 1) for f in fields])
        struct_def += "\n"
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name
        body = "\n".join([self.visit(b) for b in node.body])
        return f"{struct_def}\n{body}"

    def visit_IntEnum(self, node) -> str:
        fields = []
        for member, var in node.class_assignments.items():
            var = self.visit(var)
            if var == "auto()":
                fields.append(f"{member},")
            else:
                fields.append(f"{member} = {var},")
        fields = "\n".join([self.indent(f) for f in fields])
        return f"type {node.name} = enum\n{fields}\n\n"

    def visit_IntFlag(self, node) -> str:
        fields = []
        for member, var in node.class_assignments.items():
            var = self.visit(var)
            if var == "auto()":
                fields.append(f"{member},")
            else:
                fields.append(f"{member} = {var},")
        fields = "\n".join([self.indent(f, level=2) for f in fields])
        # flags = self.indent(f"{node.name}Flags = set[{node.name}]")
        return "\n".join(
            [
                "type",
                self.indent(f"{node.name} = enum"),
                f"{fields}",
                # f"{flags}",
                "",
            ]
        )

    def visit_StrEnum(self, node) -> str:
        fields = []
        for member, var in node.class_assignments.items():
            var = self.visit(var)
            if var == "auto()":
                fields.append(f"{member},")
            else:
                fields.append(f"{member} = {var},")
        fields = "\n".join([self.indent(f) for f in fields])
        return f"type {node.name} = enum\n{fields}\n\n"

    def _import(self, name: str) -> str:
        return f"import {name}"

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        names = ", ".join(names)
        if len(names) == 1:
            # TODO: make this more generic so it works for len(names) > 1
            name = names[0]
            lookup = f"{module_name}.{name}"
            if lookup in MODULE_DISPATCH_TABLE:
                mojo_module_name, mojo_name = MODULE_DISPATCH_TABLE[lookup]
                return f"from {mojo_module_name} import {mojo_name}"
        return f"from {module_name} import {names}"

    def visit_List(self, node) -> str:
        elements = [self.visit(e) for e in node.elts]
        elements = ", ".join(elements)
        return f"List({elements})"

    def visit_Set(self, node) -> str:
        self._usings.add("sets")
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"toHashSet([{elements_str}])"

    def visit_Dict(self, node) -> str:
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(k) for k in node.values]
        kv_pairs = ", ".join([f"{k}: {v}" for k, v in zip(keys, values)])
        return f"{{{kv_pairs}}}"

    def visit_Subscript(self, node) -> str:
        value = self.visit(node.value)
        index = self.visit(node.slice)
        if hasattr(node, "is_annotation"):
            if value in self._container_type_map:
                value = self._container_type_map[value]
            if value == "Tuple":
                return f"({index})"
            return f"{value}[{index}]"
        return f"{value}[{index}]"

    def visit_Index(self, node) -> str:
        return self.visit(node.value)

    def visit_Slice(self, node) -> str:
        lower = ""
        if node.lower:
            lower = self.visit(node.lower)
        upper = ""
        if node.upper:
            upper = self.visit(node.upper)

        return f"{lower}..{upper}"

    def visit_Tuple(self, node) -> str:
        elts = [self.visit(e) for e in node.elts]
        elts = ", ".join(elts)
        if hasattr(node, "is_annotation"):
            return elts
        return f"({elts})"

    def visit_Assert(self, node) -> str:
        self._usings.add("testing")
        return f"testing.assert_true({self.visit(node.test)})"

    def visit_AnnAssign(self, node) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        kw = "var"  # mojo 24.1 removed support for let
        if type_str == self._default_type:
            return f"{kw} {target} = {val}"
        return f"{kw} {target}: {type_str} = {val}"

    def visit_Assign(self, node) -> str:
        lines = [self._visit_AssignOne(node, target) for target in node.targets]
        if len(lines) > 1:
            line0 = lines[0]
            lines = [self.indent(line, node.level) for line in lines]
            lines[0] = line0  # parent node is going to add indentation
        return "\n".join(lines)

    def _visit_AssignOne(self, node, target) -> str:
        kw = "var"  # mojo 24.1 removed support for let

        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            elts_str = ", ".join(elts)
            value = self.visit(node.value)
            return f"({elts_str}) = {value}"

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            target_id = self.visit(target)
            if target_id in outer_if.common_vars:
                value = self.visit(node.value)
                return f"{target_id} = {value}"

        if isinstance(target, ast.Subscript) or isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value}"

        definition = node.scopes.parent_scopes.find(get_id(target))
        if definition is None:
            definition = node.scopes.find(get_id(target))
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value}"
        else:
            target = self.visit(target)
            value = self.visit(node.value)

            return f"{kw} {target} = {value}"

    def visit_Yield(self, node) -> str:
        if node.value is not None:
            value = self.visit(node.value)
            return f"yield {value}"
        return "yield nil"

    def visit_Print(self, node) -> str:
        buf = []
        for n in node.values:
            value = self.visit(n)
            buf.append(f'print("{{:?}}",{value})')
        return "\n".join(buf)

    def visit_IfExp(self, node) -> str:
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"if {test}: {body} else: {orelse}"
