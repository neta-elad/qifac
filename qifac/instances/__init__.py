import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import TextIO

from ..instantiation_tree import Forest
from ..metadata import Metadata


def show(smt_file: TextIO) -> Forest:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = dir_path / "input.smt2"

        with open(input_path, "w") as input_file:
            shutil.copyfileobj(smt_file, input_file)

        log_path = dir_path / "z3.log"
        subprocess.run(
            [
                Metadata.default().z3,
                "trace=true",
                f"trace_file_name={log_path}",
                str(input_path),
            ],
            capture_output=True,
            text=True,
        )

        instances_path = dir_path / "instances.txt"

        subprocess.run(
            [
                Metadata.default().z3tracer,
                "--skip-z3-version-check",
                "--instantiation-tree",
                str(instances_path),
                str(log_path),
            ],
            capture_output=True,
            text=True,
        )

        return Forest.parse(instances_path.read_text().splitlines())
