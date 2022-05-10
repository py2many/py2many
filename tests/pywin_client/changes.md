## File changes
- changed `import winerror` to `import ext_modules.winerror as winerror` in files:
  - `__init__.py`
  - `dynamic.py`
  - `build.py`
- changed `import string` to `import ext_modules.string as string` in files:
  - `build.py`
- changed `from keyword import iskeyword` to `from ext_modules.keyword import iskeyword` in files:
  - build.py