#!/usr/bin/env python3
try:
    from distutils.core import setup
except ImportError:
    from setuptools import setup

__version__ = "0.5.1"

install_requires = ["toposort", "astor; python_version<'3.9'"]
setup_requires = []
tests_require = ["pytest", "unittest-expander", "argparse_dataclass"]

with open("README.md") as readme_file:
    readme = readme_file.read()

packages = [
    "py2many",
    "pycpp",
    "pyd",
    "pydart",
    "pygo",
    "pyjl",
    "pykt",
    "pynim",
    "pyrs",
    "pysmt",
    "pyv",
]
package_dir = dict((f"py2many.{pkg}", pkg) for pkg in packages if pkg != "py2many")
package_dir["py2many"] = "py2many"
packages = sorted(package_dir.keys())

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
    packages=packages,
    package_dir=package_dir,
    license="MIT",
    classifiers=[
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Topic :: Software Development",
        "Topic :: Utilities",
    ],
    test_suite="tests",
    entry_points={"console_scripts": ["py2many=py2many.cli:main"]},
)
