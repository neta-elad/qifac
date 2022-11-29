import shutil
import sys
from typing import TextIO

import click

from . import uglify as do_uglify

@click.group
def smt():
    pass

@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def uglify(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_uglify(smt_file), output)