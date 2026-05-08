import os
import re
import sys


def hide_literals(line):
    """
    Replaces strings and comments with placeholders.
    Returns (cleaned_line, placeholders_dict)
    """
    placeholders = {}

    def repl(match):
        key = f"__VV_PH_{len(placeholders)}__"
        placeholders[key] = match.group(0)
        return key

    # Pattern for strings (double and single quotes) and comments
    # We prioritize matching strings first so // inside string is kept
    pattern = r'("[^"]*?"|\'[^\']*?\')|(//.*)'

    # clean_line = re.sub(pattern, repl, line)
    # re.sub with groups is tricky if we want to capture the whole match.
    # The pattern (A)|(B) matches A or B. match.group(0) is the whole match.

    clean_line = re.sub(pattern, repl, line)
    return clean_line, placeholders


def restore_literals(line, placeholders):
    """Restores placeholders in the line."""
    for key, value in placeholders.items():
        line = line.replace(key, value)
    return line


def format_operators(line):
    """Adds spaces around binary operators."""
    # List of operators to pad.
    # Order matters: longer (multi-char) operators first!
    operators = [
        "==",
        "!=",
        ">=",
        "<=",
        "&&",
        "||",
        "+=",
        "-=",
        "*=",
        "/=",
        "%=",
        ":=",
        "=",
    ]
    # We don't do + - * / % < > to avoid unary/generic issues in this simple script.

    # We want to replace valid operators with " OP ".
    # We must ensuring we don't double space if already spaced,
    # AND we don't break things like `==` into ` = = ` (handled by sorting).

    # Regex: \s*(OP)\s*  -> " \1 "
    # We construct one big regex: \s*(==|!=|...)\s*

    # Escape operators for regex
    ops_escaped = [re.escape(op) for op in operators]
    pattern_str = r"\s*(" + "|".join(ops_escaped) + r")\s*"

    return re.sub(pattern_str, r" \1 ", line)


def format_v(content):
    lines = content.splitlines()
    formatted_lines = []
    level = 0

    for line in lines:
        stripped = line.strip()
        if not stripped:
            formatted_lines.append("")
            continue

        # 1. Hide strings/comments to protect them during formatting/analysis
        clean_code, placeholders = hide_literals(stripped)

        # 2. Format operators (on cleaned code)
        clean_code = format_operators(clean_code)

        # 3. Analyze braces for indentation (on cleaned code)
        # Note: clean_code now has placeholders like __VV_PH_0__, no braces in them
        n_open = clean_code.count("{")
        n_close = clean_code.count("}")

        # 4. Determine indentation
        this_indent = level

        # Simple dedent deduction handling
        # If line starts with closing brace/paren, dedent this line
        # We check the CLEAN code for start token
        if clean_code.strip().startswith("}") or clean_code.strip().startswith(")"):
            this_indent -= 1

        if this_indent < 0:
            this_indent = 0

        # 5. Reconstruct line
        # Restore literals into the formatted clean_code
        final_line_content = restore_literals(clean_code, placeholders)

        # trim again just in case operators added spaces at ends
        final_line_content = final_line_content.strip()

        formatted_lines.append("    " * this_indent + final_line_content)

        # 6. Update level for next line
        level += n_open - n_close

        if level < 0:
            level = 0

    return "\n".join(formatted_lines) + "\n"


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python vformat.py <file.v>")
        sys.exit(1)

    path = sys.argv[1]
    if not os.path.exists(path):
        print(f"Error: File {path} not found")
        sys.exit(1)

    with open(path, "r", encoding="utf-8") as f:
        content = f.read()

    new_content = format_v(content)

    with open(path, "w", encoding="utf-8") as f:
        f.write(new_content)
    print(f"Formatted {path}")
