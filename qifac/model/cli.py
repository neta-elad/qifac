import sys
from typing import TextIO

import click

from . import get_model_size, clean
from ..utils import smt_file_read_write


@click.group
def model() -> None:
    pass

smt_file_read_write(model, clean)


@model.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
def size(smt_file: TextIO) -> None:
    low, high = get_model_size(smt_file)
    if low == high:
        print(low)
    else:
        print(f"{low}-{high}")
