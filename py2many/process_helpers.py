import os
import sys


# Copy of distutils.spawn, removed in Python 3.12
def find_executable(executable, path=None):
    """Tries to find 'executable' in the directories listed in 'path'.

    A string listing directories separated by 'os.pathsep'; defaults to
    os.environ['PATH'].  Returns the complete filename or None if not found.
    On Windows the Windows executable extensions (PATHEXT, e.g. .exe/.bat/.cmd)
    are tried for a bare name, so launchers like jlfmt.bat are found.
    """
    # An explicit path to an existing file (any extension) is used as-is.
    if os.path.isfile(executable):
        return executable

    _, ext = os.path.splitext(executable)
    if sys.platform == "win32" and not ext:
        exts = os.environ.get("PATHEXT", ".EXE;.BAT;.CMD;.COM").split(os.pathsep)
    else:
        exts = [""]

    if path is None:
        path = os.environ.get("PATH", None)
        if path is None:
            try:
                path = os.confstr("CS_PATH")
            except (AttributeError, ValueError):
                # os.confstr() or CS_PATH is not available
                path = os.defpath
        # bpo-35755: Don't use os.defpath if the PATH environment variable is
        # set to an empty string

    # PATH='' doesn't match, whereas PATH=':' looks in the current directory
    if not path:
        return None

    for p in path.split(os.pathsep):
        base = os.path.join(p, executable)
        for e in exts:
            f = base + e
            if os.path.isfile(f):
                # the file exists, we have a shot at spawn working
                return f
    return None
