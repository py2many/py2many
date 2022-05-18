using Pandas
include("win32com_/client/gencache.jl")

using pathlib: Path

df::pandas.DataFrame = read_csv(
    pandas,
    "https://github.com/chris1610/pbpython/blob/master/data/sample-sales-tax.csv?raw=True",
)
out_file = pwd() / "tests/pywin/tax_summary.xlsx"
df_summary::pandas.DataFrame = sum(groupby("category")[("ext price", "Tax amount")+1])
to_excel(out_file)
excel = EnsureDispatch(gencache, "Excel.Application")
excel.Visible = true
Open(excel.Workbooks, out_file)
_ = input("Press enter to close Excel")
Quit(excel.Application)
