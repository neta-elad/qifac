import io
import random
from typing import Dict, TextIO


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


def rename_instantiations(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    after_main_assert = False

    for line in smt_file.readlines():
        if "!MAIN-ASSERT!" in line:
            after_main_assert = True

        if after_main_assert:
            line = line.replace("!QUANTIFIED!", "!INST!")

        buffer.write(line)

    buffer.seek(0)
    return buffer


def add_assertions_from(smt_file: TextIO, added: TextIO) -> TextIO:
    buffer = io.StringIO()
    for line in smt_file.readlines():
        if line.startswith("(check-sat"):
            for added_line in added.readlines():
                if added_line.startswith("(assert"):
                    buffer.write(added_line)
        buffer.write(line)

    buffer.seek(0)
    return buffer
