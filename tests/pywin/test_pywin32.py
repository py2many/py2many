
import win32com_.client.gencache as gencache
import pandas
from pathlib import Path
import pandas.core.groupby.generic #Added for inference

# Read in the remote data file
df: pandas.DataFrame = pandas.read_csv("https://github.com/chris1610/pbpython/blob/master/data/sample-sales-tax.csv?raw=True")

# Define the full path for the output file
out_file = Path.cwd() / "tests/pywin/tax_summary.xlsx"
# Do some summary calcs
# In the real world, this would likely be much more involved
df_summary: pandas.DataFrame = df.groupby('category')['ext price', 'Tax amount'].sum()

# Save the file as Excel
df_summary.to_excel(out_file)

# Open up Excel and make it visible
excel = gencache.EnsureDispatch('Excel.Application')
excel.Visible = True

# Open up the file
excel.Workbooks.Open(out_file)

# Wait before closing it
_ = input("Press enter to close Excel")
excel.Application.Quit()