
PY2MANY=$(HOME)/.local/bin/py2many

d:
	$(PY2MANY) --d=1 tests/cases/fib.py
	dmd tests/cases/fib.d
	./fib


kt:
	$(PY2MANY) --kotlin=1 tests/cases/fib.py
	kotlinc  tests/cases/fib.kt  -include-runtime -d hello.jar
	java -jar hello.jar

setup:
	./setup.py install --user  # installs to $HOME/.local
