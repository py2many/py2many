import argparse
import re
import sys
from pathlib import Path
from typing import List, Optional

from .language import LanguageSettings

if sys.platform == "darwin":  # macOS
    from . import macosx_llm as llm
else:
    import llm


def extract_code(text):
    pattern = r"```(\w+)\n(.*?)```"
    match = re.search(pattern, text, re.DOTALL)
    if match:
        return match.group(2).strip()
    else:
        return None


def llm_transpile(
    filenames: List[Path],
    sources: List[str],
    settings: LanguageSettings,
    args: Optional[argparse.Namespace] = None,
):
    outputs = {}
    successful = []
    model = llm.get_model(args.llm_model)
    for filename, source in zip(filenames, sources):
        target = settings.display_name
        prompt = f"""Transpile the following file from python to {target}. Enclose the code in triple backticks.

                   {source}"""
        response = model.prompt(prompt)
        code = extract_code(response.text())
        if code is None:
            code = "FAILED"
        outputs[filename] = code

    # return output in the same order as input
    output_list = [outputs[f] for f in filenames]
    return output_list, successful
