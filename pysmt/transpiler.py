import ast
from typing import List

from py2many.analysis import get_id, is_ellipsis, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import AstNotImplementedError, AstTypeNotSupported
from py2many.tracer import defined_before

from .clike import CLikeTranspiler


class SmtTranspiler(CLikeTranspiler):
    NAME = "smt"

    def __init__(self, indent=2):
        super().__init__()
        self._indent = " " * indent
        self._default_type = "var"
        if "math" in self._ignored_module_set:
            self._ignored_module_set.remove("math")

    def indent(self, code, level=1):
        return self._indent * level + code

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"import {mod}" for mod in usings)
        return uses

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"(_ {value_type} {index_type})"

    def comment(self, text):
        return f";; {text}\n"

    def _visit_DeclareFunc(self, node, return_type):
        return f"(declare-fun {node.name}() {return_type})"

    def visit_FunctionDef(self, node):
        body = "\n".join([self.indent(self.visit(n)) for n in node.body])
        typenames, args = self.visit(node.args)

        args_list = []

        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]

            args_list.append(f"(declare-const {arg} {typename})")

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                typename = self._typename_from_annotation(node, attr="returns")
                return_type = f" {typename}"
            else:
                return_type = ""

        if len(node.body) == 1 and is_ellipsis(node.body[0]):
            return self._visit_DeclareFunc(node, return_type)

        args = "\n".join(args_list)
        funcdef = f"define-fun {node.name}() {return_type}"
        return f"{args}\n({funcdef}\n{body})\n"

    def visit_Return(self, node):
        if node.value:
            ret = self.visit(node.value)

            return f"return {ret}"
        return "return"

    def visit_arg(self, node):
        id = get_id(node)
        typename = "T"
        if node.annotation:
            typename = self._typename_from_annotation(node)
        return (typename, id)

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
        if vargs:
            args = " " + " ".join(vargs)
        else:
            args = ""
        return f"({fname}{args})"

    def visit_sealed_class(self, node):
        variants = []
        for member, var in node.class_assignments.items():
            member_id = get_id(member)
            typename, default_val = node.declarations_with_defaults.get(member_id, None)
            if typename == self._default_type:
                variants.append("(None)")
            else:
                innerv = []
                definition = node.scopes.parent_scopes.find(typename)
                if definition is None:
                    raise AstTypeNotSupported(f"{typename}", node)
                for member, var in definition.class_assignments.items():
                    member_id = get_id(member)
                    member_type = definition.declarations.get(member_id)
                    innerv.append(f"({member_id} {member_type})")
                innerv_str = f"{''.join(innerv)}"
                cons = typename.lower()
                variants.append(f"({cons} {innerv_str})")

        variants_str = f"({''.join(variants)})"
        return f"(declare-datatypes (({node.name} 0)) ({variants_str}))"

    def visit_ClassDef(self, node):
        extractor = DeclarationExtractor(SmtTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.declarations_with_defaults = extractor.get_declarations_with_defaults()
        node.class_assignments = extractor.class_assignments

        decorators = [get_id(d) for d in node.decorator_list]
        if "sealed" in decorators:
            # TODO: handle cases where sealed is stacked with other decorators
            return self.visit_sealed_class(node)

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = f"ST{index}"
                index += 1
            fields.append(f"{declaration}: {typename}")

        return ""

    def _import(self, name: str) -> str:
        return f"import {name}"

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        names = ", ".join(names)
        return f"from {module_name} import {names}"

    def visit_Tuple(self, node):
        elts = [self.visit(e) for e in node.elts]
        elts = " ".join(elts)
        if hasattr(node, "is_annotation"):
            return elts
        return f"({elts})"

    def visit_Assert(self, node):
        expr = self.visit(node.test)
        return f"(assert {expr})"

    def visit_AnnAssign(self, node):
        target, type_str, val = super().visit_AnnAssign(node)
        if val == None:
            return f"(declare-const {target} {type_str})"
        else:
            raise AstNotImplementedError(f"{val} can't be assigned", node)

    def visit_Assign(self, node):
        lines = [self._visit_AssignOne(node, target) for target in node.targets]
        if len(lines) > 1:
            line0 = lines[0]
            lines = [self.indent(line, node.level) for line in lines]
            lines[0] = line0  # parent node is going to add indentation
        return "\n".join(lines)

    def _visit_AssignOne(self, node, target):
        kw = "setq" if is_mutable(node.scopes, get_id(target)) else "let"

        if isinstance(target, ast.Subscript) or isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"(setq {target} {value})"

        definition = node.scopes.parent_scopes.find(get_id(target))
        if definition is None:
            definition = node.scopes.find(get_id(target))
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"(setq {target} {value})"
        else:
            target = self.visit(target)
            value = self.visit(node.value)

            return f"({kw} ({target} {value}))"
