from typing import Callable, Dict, Tuple, Union

import torch

class JuliaExternalModulePlugins():
    def visit_torch_zeros(self, node, vargs):
        self._usings.add("Torch")
        # print(node.args)
        # print(f"Torch.zeros({', '.join(vargs)})")
        return f"Torch.zeros({', '.join(vargs)})"

    def visit_torch_zeros_numpy(self, node, vargs):
        self._usings.add("Torch")
        # return f"Torch.zeros.numpy({', '.join(vargs)})"
        return f"{vargs[0]}"


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    torch.zeros: (JuliaExternalModulePlugins.visit_torch_zeros, True),
    torch.Tensor.numpy: (JuliaExternalModulePlugins.visit_torch_zeros_numpy, True)
}

EXTERNAL_TYPE_MAP = {
    torch.Tensor: "" # Temporary
}

FUNC_TYPE_MAP = {
    torch.zeros: lambda self, node, vargs: "torch.Tensor"
}

IGNORED_MODULE_SET = set(["torch"])