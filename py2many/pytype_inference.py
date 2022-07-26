import os
from pathlib import PosixPath
from pytype import analyze, errors, config, load_pytd
from pytype.pytd import pytd_utils
from pytype.tools.merge_pyi import merge_pyi

# Args class taken from pytd_utils
class Args:

  def __init__(self, as_comments=False):
    self.as_comments = as_comments

  @property
  def expected_ext(self):
    """Extension of expected filename."""
    exts = {
        0: 'pep484',
        1: 'comment',
    }
    return exts[int(self.as_comments)] + '.py'

log = errors.ErrorLog()

def pytype_annotate_and_merge(src: str, basedir: PosixPath, filename: PosixPath):
    options = config.Options.create()
    pyi_dir = f"{os.getcwd()}{os.sep}{basedir}_pyi" \
        if os.path.isdir(f"{os.getcwd()}{os.sep}{basedir}") \
        else f"{os.getcwd()}{os.sep}{basedir.parent}"
    pyi_file = f"{pyi_dir}{os.sep}{filename.stem}.pyi"
    # Get .pyi data
    if os.path.isdir(pyi_dir) and \
            os.path.isfile(pyi_file):
        with open(pyi_file, "r") as f:
            pyi_src = f.read()
    else:
        # typed_ast is an instance of TypeDeclUnit
        typed_ast, _ = analyze.infer_types(src, log, 
            options, load_pytd.Loader(options))
        pyi_src = pytd_utils.Print(typed_ast)
    # Write pyi_src to .pyi file if necessary
    if not os.path.isfile(pyi_file):
        if not os.path.isdir(pyi_dir):
            os.mkdir(pyi_dir)
        with open(pyi_file, "w") as f:
            f.write(pyi_src)
    args = Args(as_comments = 1)
    annotated_src = merge_pyi.annotate_string(args, src, pyi_src)
    return annotated_src
