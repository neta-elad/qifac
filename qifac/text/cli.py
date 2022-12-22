import shutil
import sys
from typing import Tuple, List, TextIO, Iterable

import click

from ..utils import smt_file_read_write

from . import remove_comments, sample


@click.group
def text() -> None:
    pass


smt_file_read_write(text, remove_comments, "clear")


@text.command("sample")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--samples", "-s", type=(str, int), multiple=True)
def wrap_sample(
    smt_file: TextIO, output: TextIO, samples: Iterable[Tuple[str, int]]
) -> None:
    shutil.copyfileobj(sample(smt_file, dict(samples)), output)
