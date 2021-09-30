cd ../
for /f %%f in ('dir pyjl\tests\*.py /d') do py2many.py --julia=1 pyjl\tests\%%f
ECHO All tests ran successfully!
PAUSE