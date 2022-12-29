import sys
from typing import TextIO

import click

from ..utils import smt_file_read_write
from . import count_quantifiers, count_symbols, count_terms


@click.group
def count() -> None:
    pass


smt_file_read_write(count, count_quantifiers, "quantifiers")


@count.command("symbols")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.option('--show', '-s', is_flag=True, default=False)
def wrap_symbols(smt_file: TextIO, show: bool) -> None:
    count_symbols(smt_file, show)


@count.command("terms")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.option('--show', '-s', is_flag=True, default=False)
def wrap_terms(smt_file: TextIO, show: bool) -> None:
    count_terms(smt_file, show)
