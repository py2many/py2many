#!/usr/bin/env python3
"""Emit a markdown table of languages and how many cases in tests/expected/
have been transpiled to each.

Stdlib-only so it can run in the lint job without installing py2many. The
extension -> language-name map mirrors py2many's registry (py2many/registry.py);
keep it in sync when a backend is added or removed. Run from anywhere:

    python scripts/lang_table.py            # print to stdout
    python scripts/lang_table.py > LANGUAGES.md
"""

import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
EXPECTED_DIR = REPO_ROOT / "tests" / "expected"

SMT_EXT = ".smt"

# Common cases worth flagging when a backend can't transpile them.
KEY_CASES = ["coverage", "stdio", "bubble_sort", "comb_sort", "sys_argv", "sys_exit"]

# Extension -> display name, mirroring py2many/registry.py.
EXT_TO_LANGUAGE = {
    ".py": "Python",
    ".cpp": "C++",
    ".rs": "Rust",
    ".jl": "Julia",
    ".kt": "Kotlin",
    ".lean": "Lean",
    ".nim": "Nim",
    ".mojo": "Mojo",
    ".d": "D",
    ".dart": "Dart",
    ".go": "Go",
    ".v": "V",
    ".smt": "SMT",
    ".zig": "Zig",
}


def language_rows():
    # Group each case's expected outputs by case stem (e.g. "fib" -> {".rs"...}).
    by_stem = defaultdict(set)
    for path in EXPECTED_DIR.iterdir():
        if path.is_file() and path.suffix in EXT_TO_LANGUAGE:
            by_stem[path.stem].add(path.suffix)
    # SMT-only cases (pysmt constraint problems) are not real programs in the
    # other backends, so they only count towards SMT -- exclude their stems
    # from every other language even if stray output is ever committed.
    smt_only = {stem for stem, exts in by_stem.items() if SMT_EXT in exts}
    counts = Counter()
    for stem, exts in by_stem.items():
        for ext in exts:
            if ext != SMT_EXT and stem in smt_only:
                continue
            counts[EXT_TO_LANGUAGE[ext]] += 1
    rows = []
    for ext, lang in EXT_TO_LANGUAGE.items():
        if lang not in counts:
            continue
        missing = [c for c in KEY_CASES if ext not in by_stem.get(c, set())]
        rows.append((lang, counts[lang], missing))
    # Order by number of cases descending, then language name for ties.
    rows.sort(key=lambda r: (-r[1], r[0]))
    return rows


def render_table(rows):
    lines = ["| Language | Cases | Notable failures |", "| --- | --- | --- |"]
    for lang, n, missing in rows:
        lines.append(f"| {lang} | {n} | {', '.join(missing)} |")
    return "\n".join(lines) + "\n"


def main():
    sys.stdout.write(render_table(language_rows()))


if __name__ == "__main__":
    main()
