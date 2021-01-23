import io
import re
from setuptools import setup, find_packages

__version__ = "0.0.0"

install_requires = []
setup_requires = []
tests_require = ["pytest"]

setup(
    name="pyrs",
    version=__version__,
    description="Python to Rust transpiler.",
    long_description="""
Python to Rust transpiler

This project started as Python to Rust syntax converter. It is not
aimed at producing ready-to-compile code, but some basic stuff can be
compiled easily.

It generates unidiomatic non-optimized code with unnecessary
allocations, but can reduce amount of edits you have to do when
porting Python projects.

Only basic subset of Python is supported right now and the end goal is
to support common cases at least as a placeholders.

The project is in experimental, so it may crash or silently skip some
statements, so be careful.

Based on Lukas Martinelli Py14
(https://github.com/lukasmartinelli/py14) and Py14/python-3
(https://github.com/ProgVal/py14/tree/python-3) branch by Valentin
Lorentz.
    """,
    author="Julian Konchunas",
    author_email="konchunas@gmail.com",
    python_requires=">=3.0.0",
    url="http://github.com/konchunas/pyrs",
    install_requires=install_requires,
    setup_requires=setup_requires,
    tests_require=tests_require,
    packages=find_packages(exclude=["docs", "examples", "tests"]),
    scripts=["pyrs.py"],
    license="MIT",
    classifiers=[
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Topic :: Software Development",
        "Topic :: Utilities",
    ],
    test_suite="tests",
)
