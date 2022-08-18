import ast
import gzip
from typing import Callable, Dict, Tuple, Union


class JuliaExternalModulePlugins:
    def visit_gzipopen(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(self)
        if vargs:
            return f"GZip.open({', '.join(vargs)})"
        # elif len(vargs) == 2:
        #     return f"GZip.open({vargs[0]}, gzmode = {vargs[1]})"
        # elif len(vargs) == 3:
        #     return f"GZip.open({vargs[0]}, gzmode = {vargs[1]}, buf_size = {vargs[2]})"
        return "GZip.open"

    def visit_gzipcompress(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(self)
        return f"#Unsupported\nGZip.compress"

    def visit_gzipdecompress(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(self)
        return f"#Unsupported\nGZip.decompress"

    def visit_gzipBadGzipFile(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(self)
        # TODO: Temporary
        f'GZError(-1, "gzopen failed")'

    def _generic_gzip_visit(self):
        self._usings.add("GZip")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    gzip.open: (JuliaExternalModulePlugins.visit_gzipopen, True),
    gzip.compress: (JuliaExternalModulePlugins.visit_gzipcompress, True),
    gzip.decompress: (JuliaExternalModulePlugins.visit_gzipdecompress, True),
    gzip.BadGzipFile: (JuliaExternalModulePlugins.visit_gzipBadGzipFile, True),
}

IGNORED_MODULE_SET = set(["gzip"])
