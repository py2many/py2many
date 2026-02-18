# Transpiler Architecture

## Overview
py2many converts Python source code to multiple target languages using a modular transpiler architecture.

## Key Components

### Base Transpiler
- `py2many/transpilers/` contains all transpiler implementations
- Each language has its own transpiler class extending a common base

## Adding New Language Support

1. **Create Transpiler Class**
   - Create `py2many/transpilers/<language>.py`
   - Inherit from appropriate base class
   - Implement language-specific transformations

2. **Update CLI**
   - Add language flag in `py2many/__main__.py`

3. **Add Tests**
   - Create test cases in `tests/cases/`
   - Add expected output in `tests/expected/`

4. **Update Documentation**
   - Add language to README.md

## Transpilation Process

1. Parse Python AST using `ast` module
2. Traverse AST and apply transformations
3. Emit target language code
4. Handle type inference and conversions

## Important Considerations

- Use explicit returns (no implicit Python returns)
- Handle Python-specific features (comprehensions, decorators)
- Test compilation in target language
