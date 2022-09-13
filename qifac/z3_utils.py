import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import TextIO

from .metadata import Metadata


def run_z3(smt_file: TextIO, *options: str) -> str:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        return subprocess.run(
            [Metadata.default().z3, str(input_path)] + list(options),
            capture_output=True,
            text=True,
        ).stdout.strip()
