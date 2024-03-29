import io
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Optional, TextIO

from ..metadata import Metadata


def cleanup(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    for line in smt_file.readlines():

        stripped = line.strip()
        if "(push " in stripped or "(pop" in stripped:
            continue

        buffer.write(line)

        if "(check-sat)" in stripped:
            break

    buffer.seek(0)

    return buffer


def clean_errors(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    with tempfile.TemporaryDirectory() as tmpdir:
        input_path = Path(tmpdir) / "input.smt"
        with open(input_path, "w") as input_file:
            shutil.copyfileobj(smt_file, input_file)

        result = subprocess.run(
            [
                Metadata.default().z3,
                str(input_path),
            ],
            capture_output=True,
            text=True,
        ).stdout

        lines_to_remove = set()

        for line in result.splitlines():
            line_number = parse_error_line(line)
            if line_number is not None:
                lines_to_remove.add(line_number)

    smt_file.seek(0)
    for line_number, line in enumerate(smt_file.readlines(), start=1):
        if line_number in lines_to_remove:
            continue

        if "model-del" in line:
            continue

        buffer.write(line)

    buffer.seek(0)

    return buffer


def parse_error_line(line: str) -> Optional[int]:
    match = re.match(r'\(error "line (\d+)', line)

    if match is not None:
        return int(match[1])

    return None


def unify_lines(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()
    lines = [line.strip() for line in smt_file.readlines()]
    unified_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("(assert ") and line.count("(") != line.count(")"):
            j = i + 1
            unified_line = line
            while j < len(lines) and unified_line.count("(") != unified_line.count(")"):
                unified_line += " " + lines[j]
                j += 1
            assert unified_line.count("(") == unified_line.count(")")
            unified_lines.append(unified_line)
            i = j
        else:
            unified_lines.append(line)
            i += 1
    buffer.write("\n".join(unified_lines))
    buffer.seek(0)
    return buffer
