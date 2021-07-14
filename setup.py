#!/usr/bin/env python3

from setuptools import setup, find_packages

__version__ = "0.3"

install_requires = ["toposort", "astor; python_version<'3.9'"]
setup_requires = []
tests_require = ["pytest", "unittest-expander", "argparse_dataclass"]

with open("README.md") as readme_file:
    readme = readme_file.read()

setup(
    name="py2many",
    version=__version__,
    description="Python to CLike language transpiler.",
    long_description=readme + "\n\n",
    long_description_content_type="text/markdown",
    author="Arun Sharma",
    python_requires=">=3.8",
    url="https://github.com/adsharma/py2many",
    install_requires=install_requires,
    setup_requires=setup_requires,
    tests_require=tests_require,
    packages=find_packages(
        exclude=["docs", "examples", "tests", "tests*", "pycpp.tests", "pyrs.tests"]
    ),
    license="MIT",
    classifiers=[
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Topic :: Software Development",
        "Topic :: Utilities",
    ],
    test_suite="tests",
    entry_points={
        "console_scripts": ["py2many=py2many.cli:main"],
    },
)
