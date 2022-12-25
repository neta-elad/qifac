import shutil
import sys
from pathlib import Path
from typing import TextIO

import click

from . import (
    compare_directories,
    compare_directory_instances,
    compare_files,
    compare_instances,
    manual,
    manual_compare,
    sanity,
)


@click.group
def analyze() -> None:
    pass


@analyze.command(name="compare")
@click.argument("unsat_smt_file", type=click.File("r"))
@click.argument("unknown_smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_compare_files(
    unsat_smt_file: TextIO, unknown_smt_file: TextIO, output: TextIO
) -> None:
    shutil.copyfileobj(compare_files(unsat_smt_file, unknown_smt_file), output)


@analyze.command(name="manual-compare")
@click.argument(
    "unsat_instances", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_instances", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.Path(file_okay=False, exists=True, path_type=Path))
def wrap_manual_compare(
    unsat_instances: Path, unknown_instances: Path, output: Path
) -> None:
    manual_compare(unsat_instances, unknown_instances, output)


@analyze.command(name="manual")
@click.argument(
    "unsat_instances", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.Path(file_okay=False, exists=True, path_type=Path))
def wrap_manual(unsat_instances: Path, output: Path) -> None:
    manual(unsat_instances, output)


@analyze.command(name="instances")
@click.argument(
    "unsat_smt_file", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_smt_file", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.Path(file_okay=False, path_type=Path))
def wrap_compare_instances(
    unsat_smt_file: Path, unknown_smt_file: Path, output: Path
) -> None:
    compare_instances(unsat_smt_file, unknown_smt_file).write(output)


@analyze.command(name="sanity")
@click.argument("unsat_smt_file", type=click.File("r"))
def wrap_sanity(unsat_smt_file: TextIO) -> None:
    sanity(unsat_smt_file)


@analyze.command(name="dirs")
@click.argument(
    "unsat_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_compare_directories(
    unsat_files: Path, unknown_files: Path, output_dir: Path, output: TextIO
) -> None:
    shutil.copyfileobj(
        compare_directories(unsat_files, unknown_files, output_dir), output
    )


@analyze.command(name="instance-dirs")
@click.argument(
    "unsat_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def wrap_compare_directory_instances(
    unsat_files: Path, unknown_files: Path, output_dir: Path
) -> None:
    compare_directory_instances(unsat_files, unknown_files, output_dir)
