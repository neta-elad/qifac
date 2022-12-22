import io
import random
from typing import TextIO, Dict


def remove_comments(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    for line in smt_file.readlines():
        if not line.startswith(";"):
            buffer.write(line)

    buffer.seek(0)
    return buffer


def in_group(line: str, group: str) -> bool:
    return line.startswith("(assert") and f"!{group}!" in line


def sample(smt_file: TextIO, samples: Dict[str, int]) -> TextIO:
    lines = smt_file.readlines()

    groups = {
        group: [i for i, line in enumerate(lines) if in_group(line, group)]
        for group in samples
    }

    for group in samples:
        random.shuffle(groups[group])

    sampled = {i for group, size in samples.items() for i in groups[group][:size]}

    buffer = io.StringIO()

    for i, line in enumerate(lines):
        if not line.startswith("(assert") or i in sampled:
            buffer.write(line)

    buffer.seek(0)
    return buffer
