import ast
import gzip
from typing import Callable, Dict, Tuple, Union


class JuliaExternalModulePlugins:
    def visit_gzipopen(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(t_self)
        if vargs:
            return f"GZip.open({', '.join(vargs)})"
        # elif len(vargs) == 2:
        #     return f"GZip.open({vargs[0]}, gzmode = {vargs[1]})"
        # elif len(vargs) == 3:
        #     return f"GZip.open({vargs[0]}, gzmode = {vargs[1]}, buf_size = {vargs[2]})"
        return "GZip.open"

    def visit_gzipcompress(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(t_self)
        return f"#Unsupported\nGZip.compress"

    def visit_gzipdecompress(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(t_self)
        return f"#Unsupported\nGZip.decompress"

    def visit_gzipBadGzipFile(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._generic_gzip_visit(t_self)
        # TODO: Temporary
        f'GZError(-1, "gzopen failed")'

    def _generic_gzip_visit(t_self):
        t_self._usings.add("GZip")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    gzip.open: (JuliaExternalModulePlugins.visit_gzipopen, True),
    gzip.compress: (JuliaExternalModulePlugins.visit_gzipcompress, True),
    gzip.decompress: (JuliaExternalModulePlugins.visit_gzipdecompress, True),
    gzip.BadGzipFile: (JuliaExternalModulePlugins.visit_gzipBadGzipFile, True),
}

IGNORED_MODULE_SET = set(["gzip"])
