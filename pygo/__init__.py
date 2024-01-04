import os
from pathlib import Path

import py2many
from py2many.language import LanguageSettings

from .inference import infer_go_types
from .transpiler import (
    GoIfExpRewriter,
    GoMethodCallRewriter,
    GoNoneCompareRewriter,
    GoPropagateTypeAnnotation,
    GoTranspiler,
    GoVisibilityRewriter,
)

PY2MANY_DIR = Path(py2many.__file__).parent
ROOT_DIR = PY2MANY_DIR.parent


def settings(args, env=os.environ):
    config_filename = "revive.toml"
    CWD = Path.cwd()
    if os.path.exists(CWD / config_filename):
        revive_config = CWD / config_filename
    elif os.path.exists(ROOT_DIR / config_filename):
        revive_config = ROOT_DIR / config_filename
    else:
        revive_config = None
    return LanguageSettings(
        GoTranspiler(),
        ".go",
        "Go",
        ["gofmt", "-w"],
        None,
        [GoNoneCompareRewriter(), GoVisibilityRewriter(), GoIfExpRewriter()],
        [infer_go_types],
        [GoMethodCallRewriter(), GoPropagateTypeAnnotation()],
        linter=(
            ["revive", "--config", str(revive_config)] if revive_config else ["revive"]
        ),
    )
