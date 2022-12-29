import sys
from pathlib import Path
from typing import TextIO

import click

from .aggregate.cli import aggregate
from .analyze import pair_up_files
from .analyze.cli import analyze
from .batch.cli import batch
from .cegar import cegar as do_cegar
from .core.cli import core
from .count.cli import count
from .instances.cli import instances
from .model.cli import model
from .search.cli import search
from .smt.cli import smt
from .text.cli import text
from .typeinfo.cli import typeinfo
from .z3_utils import run_z3 as do_run_z3


@click.group
def run() -> None:
    pass


run.add_command(core)
run.add_command(instances)
run.add_command(model)
run.add_command(search)
run.add_command(text)
run.add_command(smt)
run.add_command(batch)
run.add_command(typeinfo)
run.add_command(analyze)
run.add_command(aggregate)
run.add_command(count)


@run.command(name="z3")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
def run_z3(smt_file: TextIO) -> None:
    print(do_run_z3(smt_file))


@run.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def cegar(smt_file: TextIO, output: TextIO) -> None:
    do_cegar(smt_file)

    # for assertion in asserts:
    #     output.write(f"{assertion.sexpr()}\n")


@run.command(name="pair")
@click.argument(
    "unsat_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def do_pair_up_files(unsat_files: Path, unknown_files: Path, output_dir: Path) -> None:
    pair_up_files(unsat_files, unknown_files, output_dir)


if __name__ == "__main__":
    run()
