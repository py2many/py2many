import os
import pathlib

from unittest.mock import Mock

from .language import LanguageSettings

from .python_transformer import PythonTranspiler, RestoreMainRewriter

from .rewriters import InferredAnnAssignRewriter

CI = os.environ.get("CI", "0")
if CI in ["1", "true"]:
    from .pycpp import settings as cpp_settings
    from .pydart import settings as dart_settings
    from .pygo import settings as go_settings
    from .pyjl import settings as julia_settings
    from .pykt import settings as kotlin_settings
    from .pynim import settings as nim_settings
    from .pyrs import settings as rust_settings
    from .pysmt import settings as smt_settings
    from .pyv import settings as vlang_settings
else:
    try:
        from .pycpp import settings as cpp_settings
        from .pydart import settings as dart_settings
        from .pygo import settings as go_settings
        from .pyjl import settings as julia_settings
        from .pykt import settings as kotlin_settings
        from .pynim import settings as nim_settings
        from .pyrs import settings as rust_settings
        from .pysmt import settings as smt_settings
        from .pyv import settings as vlang_settings
    except ImportError:
        from pycpp import settings as cpp_settings
        from pydart import settings as dart_settings
        from pygo import settings as go_settings
        from pyjl import settings as julia_settings
        from pykt import settings as kotlin_settings
        from pynim import settings as nim_settings
        from pyrs import settings as rust_settings
        from pysmt import settings as smt_settings
        from pyv import settings as vlang_settings


PY2MANY_DIR = pathlib.Path(__file__).parent
ROOT_DIR = PY2MANY_DIR.parent
FAKE_ARGS = Mock(indent=4)


def python_settings(args, env=os.environ):
    return LanguageSettings(
        PythonTranspiler(),
        ".py",
        "Python",
        formatter=["black"],
        rewriters=[RestoreMainRewriter()],
        post_rewriters=[InferredAnnAssignRewriter()],
    )


ALL_SETTINGS = {
    "python": python_settings,
    "cpp": cpp_settings,
    "rust": rust_settings,
    "julia": julia_settings,
    "kotlin": kotlin_settings,
    "nim": nim_settings,
    "dart": dart_settings,
    "go": go_settings,
    "vlang": vlang_settings,
    "smt": smt_settings,
}


def _get_all_settings(args, env=os.environ):
    return dict((key, func(args, env=env)) for key, func in ALL_SETTINGS.items())
