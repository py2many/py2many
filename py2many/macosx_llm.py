from dataclasses import dataclass
from typing import Any

from mlx_lm import generate, load


@dataclass
class Model:
    model: Any
    tokenizer: Any

    def prompt(self, promptq: str) -> str:
        messages = [{"role": "user", "content": promptq}]
        llm_prompt = self.tokenizer.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True
        )
        return generate(self.model, self.tokenizer, prompt=llm_prompt)


def get_model(model_name):
    model, tokenizer = load(model_name)
    return Model(model, tokenizer)
