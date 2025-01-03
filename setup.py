import sys

from setuptools import setup

version = None
with open("py2many/version.py") as f:
    for line in f.readlines():
        if line.startswith("__version__"):
            delim = '"' if '"' in line else "'"
            version = line.split(delim)[1]

install_requires = []
setup_requires = []
test_deps = ["pytest", "argparse_dataclass"]

extras = {
    "test": test_deps,
    "llm": ["mlx_llm"] if sys.platform == "darwin" else ["llm", "llm-ollama"],
}

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
    "pymojo",
    "pynim",
    "pyrs",
    "pysmt",
    "pyv",
]
package_dir = {f"py2many.{pkg}": pkg for pkg in packages if pkg != "py2many"}
package_dir["py2many"] = "py2many"
packages = sorted(package_dir.keys())

setup(
    name="py2many",
    version=version,
    description="Python to CLike language transpiler.",
    long_description=readme + "\n\n",
    long_description_content_type="text/markdown",
    author="Arun Sharma",
    python_requires=">=3.8",
    url="https://github.com/adsharma/py2many",
    install_requires=install_requires,
    setup_requires=setup_requires,
    tests_require=test_deps,
    extras_require=extras,
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
