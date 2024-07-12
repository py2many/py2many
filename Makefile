
PY2MANY=$(HOME)/.local/bin/py2many

# test files with print out OK
OK_FILES := $(shell grep -liw OK tests/cases/*.py)
OK_EXES  := $(patsubst %.py, %.exe, $(OK_FILES))

all: $(OK_EXES)

all_tests:
	@ls -l $(OK_FILES)

%.exe: %.py
	$(PY2MANY) --d=1 $<
	dmd -run $(patsubst %.py, %.d, $<) || true


kt:
	$(PY2MANY) --kotlin=1 tests/cases/fib.py
	kotlinc  tests/cases/fib.kt  -include-runtime -d hello.jar
	java -jar hello.jar

setup:
	./setup.py install --user  # installs to $HOME/.local
