import ast
from typing import List

from py2many.analysis import get_id, is_ellipsis, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import (
    AstClassUsedBeforeDeclaration,
    AstNotImplementedError,
    AstTypeNotSupported,
)
from py2many.tracer import defined_before

from .clike import CLikeTranspiler
from .inference import get_inferred_smt_type


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
        if len(args) and hasattr(node, "self_type"):
            typenames[0] = node.self_type

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
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                return_type = self._typename_from_annotation(fndef, attr="returns")
                value_type = get_inferred_smt_type(node.value)
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
            mutable = is_mutable(node.scopes, id)
            typename = self._typename_from_annotation(node)
            if mutable:
                typename = f"var {typename}"
        return (typename, id)

    def _visit_object_literal(self, node, fname: str, fndef: ast.ClassDef):
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
                vargs += [f"{kw.arg}: {value}"]
        args = ", ".join(vargs)
        return f"{fname}({args})"

    def visit_Call(self, node):
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
            args = " " + " ".join(vargs)
        else:
            args = ""
        return f"({fname}{args})"

    def visit_NameConstant(self, node):
        if node.value is None:
            return "nil"
        else:
            return super().visit_NameConstant(node)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
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

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super().visit_UnaryOp(node)

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
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        decorators = [get_id(d) for d in node.decorator_list]
        if "sealed" in decorators:
            # TODO: handle cases where sealed is stacked with other decorators
            return self.visit_sealed_class(node)

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            fields.append(f"{declaration}: {typename}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name
        return ""

    def _import(self, name: str) -> str:
        return f"import {name}"

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        names = ", ".join(names)
        return f"from {module_name} import {names}"

    def visit_Index(self, node):
        return self.visit(node.value)

    def visit_Tuple(self, node):
        elts = [self.visit(e) for e in node.elts]
        elts = " ".join(elts)
        if hasattr(node, "is_annotation"):
            return elts
        return "({0})".format(elts)

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

        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            elts_str = ", ".join(elts)
            value = self.visit(node.value)
            return f"({kw} ({elts_str})  {value})"

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            target_id = self.visit(target)
            if target_id in outer_if.common_vars:
                value = self.visit(node.value)
                return f"({kw} {target_id} {value})"

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

    def visit_Print(self, node):
        buf = []
        for n in node.values:
            value = self.visit(n)
            buf.append('println("{{:?}}",{0})'.format(value))
        return "\n".join(buf)
