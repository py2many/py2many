
import ast
from typing import Callable, Dict, Tuple, Union

try:
    import pandas
except:
    pandas = None

class JuliaExternalModulePlugins:
    def visit_pandas_readcsv(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"read_csv({vargs[1]})"

    def visit_pandas_groupby(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"groupby({vargs[1]})"

    def visit_pandas_toexcel(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"to_excel({vargs[1]})"

    def visit_pandas_dataframe_sum(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"sum({vargs[0]})"

    def _visit_pandas(t_self):
        t_self._usings.add("Pandas")

if pandas:
    FuncType = Union[Callable, str]

    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
        pandas.read_csv: (JuliaExternalModulePlugins.visit_pandas_readcsv, False),
        pandas.DataFrame.groupby: (JuliaExternalModulePlugins.visit_pandas_groupby, False),
        pandas.DataFrame.to_excel: (JuliaExternalModulePlugins.visit_pandas_toexcel, False),
        pandas.core.groupby.generic.DataFrameGroupBy.sum: (
            JuliaExternalModulePlugins.visit_pandas_dataframe_sum,
            False,
        ),
    }

IGNORED_MODULE_SET = set([
    "pandas"
]) 