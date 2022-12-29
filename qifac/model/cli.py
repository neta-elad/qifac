import sys
from typing import TextIO

import click

from . import get_model_size


@click.group
def model() -> None:
    pass


@model.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
def size(smt_file: TextIO) -> None:
    low, high = get_model_size(smt_file)
    if low == high:
        print(low)
    else:
        print(f"{low}-{high}")
