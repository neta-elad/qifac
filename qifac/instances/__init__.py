import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Optional, Set, TextIO

import click

from ..instantiation_tree import Forest
from ..metadata import Metadata
from .compare import compare


@click.group
def instances() -> None:
    pass


@instances.command
@click.argument("smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), required=False, default=None)
def show(smt_file: TextIO, output: Optional[TextIO]) -> Forest:
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

        if output is not None:
            with open(instances_path, "r") as instances_file:
                shutil.copyfileobj(instances_file, output)

        return Forest.parse(instances_path.read_text().splitlines())


@instances.command(name="compare")
@click.argument("unsat_file", type=click.File("r"))
@click.argument("unknown_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), required=False, default=None)
def do_compare(
    unsat_file: TextIO, unknown_file: TextIO, output: Optional[TextIO]
) -> Set[str]:
    unsat_forest = Forest.parse(unsat_file.readlines())
    unknown_forest = Forest.parse(unknown_file.readlines())

    result = compare(unsat_forest, unknown_forest)

    if output is not None:
        for node in result:
            output.write(f"{node}\n")

    return result
