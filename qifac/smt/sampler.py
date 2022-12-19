import io
import random
from typing import TextIO


def is_instantiation(line: str) -> bool:
    return line.startswith("(assert") and "!QUANTIFIED!" in line
def is_quantifier_free(line: str) -> bool:
    return line.startswith("(assert") and "!QUANTIFIER-FREE!" in line

def sample(smt_file: TextIO, instantiation_size: int, quantifier_free_size: int) -> TextIO:
    lines = smt_file.read().splitlines(keepends=True)

    instantiations = [i for i, line in enumerate(lines) if is_instantiation(line)]
    quantifier_free = [i for i, line in enumerate(lines) if is_quantifier_free(line)]

    random.shuffle(instantiations)
    random.shuffle(quantifier_free)

    sampled_instantiations = set(instantiations[:instantiation_size])
    sampled_quantifier_free = set(quantifier_free[:quantifier_free_size])

    buffer = io.StringIO()

    for i, line in enumerate(lines):
        if not line.startswith("(assert") or i in sampled_instantiations | sampled_quantifier_free:
            buffer.write(line)

    buffer.seek(0)
    return buffer
