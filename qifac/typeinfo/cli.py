import sys
from pathlib import Path
from typing import TextIO

import click

from .byz3.parser import parse_smt_file
from .parser import parse_script


@click.group
def typeinfo() -> None:
    pass


@typeinfo.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def grounds(smt_file: TextIO, output: TextIO) -> None:
    type_info = parse_script(smt_file)

    for ground in type_info.grounds:
        kind = type_info.get_type(ground)

        if kind is not None:
            output.write(f"{ground}: {kind}\n")


@typeinfo.command
@click.argument(
    "smt_file", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def byz3(smt_file: Path, output: TextIO) -> None:
    type_info = parse_smt_file(smt_file)

    for ground in type_info.grounds:
        kind = type_info.get_type(ground)

        if kind is not None:
            output.write(f"{ground}: {kind}\n")
