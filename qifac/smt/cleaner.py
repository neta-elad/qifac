import io
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Optional, TextIO

from ..metadata import Metadata


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

        buffer.write(line)

    buffer.seek(0)

    return buffer


def parse_error_line(line: str) -> Optional[int]:
    match = re.match(r'\(error "line (\d+)', line)

    if match is not None:
        return int(match[1])

    return None
