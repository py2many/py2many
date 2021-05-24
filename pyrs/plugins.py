import io
import ast
import textwrap

from tempfile import NamedTemporaryFile

try:
    from argparse_dataclass import dataclass as ap_dataclass
    from argparse_dataclass import ArgumentParser
except:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class RustTranspilerPlugins:
    def visit_argparse_dataclass(self, node):
        fields = []
        for (
            declaration,
            typename_with_default,
        ) in node.declarations_with_defaults.items():
            typename, default_value = typename_with_default
            if typename == None:
                return None
            if default_value is not None and typename != "bool":
                default_value = self.visit(default_value)
                default_value = f', default_value = "{default_value}"'
            else:
                default_value = ""
            fields.append(
                f"#[structopt(short, long{default_value})]\npub {declaration}: {typename},"
            )
        fields = "\n".join(fields)
        self._usings.add("structopt::StructOpt")
        clsdef = "\n" + textwrap.dedent(
            f"""\
        #[derive(Debug, StructOpt)]
        #[structopt(name = "{self._module}", about = "Placeholder")]
        struct {node.name} {{
            {fields}
        }}
        """
        )
        return clsdef

    def visit_open(self, node, vargs):
        self._usings.add("std::fs::File")
        if len(vargs) > 1:
            self._usings.add("std::fs::OpenOptions")
            mode = vargs[1]
            opts = "OpenOptions::new()"
            is_binary = "b" in mode
            for c in mode:
                if c == "w":
                    if not is_binary:
                        self._usings.add("pylib::FileWriteString")
                    opts += ".write(true)"
                if c == "r":
                    if not is_binary:
                        self._usings.add("pylib::FileReadString")
                    opts += ".read(true)"
                if c == "a":
                    opts += ".append(true)"
                if c == "+":
                    opts += ".read(true).write(true)"
            return f"{opts}.open({vargs[0]}).unwrap()"
        return f"File::open({vargs[0]}).unwrap()"

    def visit_named_temp_file(self, node, vargs):
        node.annotation = ast.Name(id="tempfile._TemporaryFileWrapper")
        return "NamedTempFile::new().unwrap()"

    def visit_textio_read(self, node, vargs):
        # TODO
        return None

    def visit_textio_write(self, node, vargs):
        # TODO
        return None

    def visit_ap_dataclass(self, cls):
        # Do whatever transformation the decorator does to cls here
        return cls


MODULE_DISPATCH_TABLE = {"tempfile.NamedTemporaryFile": "tempfile::NamedTempFile"}

DECORATOR_DISPATCH_TABLE = {ap_dataclass: RustTranspilerPlugins.visit_ap_dataclass}

CLASS_DISPATCH_TABLE = {ap_dataclass: RustTranspilerPlugins.visit_argparse_dataclass}

FUNC_DISPATCH_TABLE = {
    # Uncomment after upstream uploads a new version
    # ArgumentParser.parse_args: lambda node: "Opts::parse_args()",
    # HACKs: remove all string based dispatch here, once we replace them with type based
    "parse_args": lambda self, node, vargs: "::from_args()",
    "temp_file.name": lambda self, node, vargs: "temp_file.path()",
    "f.read": lambda self, node, vargs: "f.read_string().unwrap",
    "f.write": lambda self, node, vargs: "f.write_string",
    open: RustTranspilerPlugins.visit_open,
    NamedTemporaryFile: RustTranspilerPlugins.visit_named_temp_file,
    io.TextIOWrapper.read: RustTranspilerPlugins.visit_textio_read,
    io.TextIOWrapper.read: RustTranspilerPlugins.visit_textio_write,
}
