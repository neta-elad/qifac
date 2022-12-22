import shutil
import sys
from typing import TextIO

import click

from . import find, find_core_with_api, instances

from ..utils import smt_file_read_write


@click.group
def core() -> None:
    pass


smt_file_read_write(core, find)
smt_file_read_write(core, find_core_with_api, "new")


@core.command(name="instances")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_instances(smt_file: TextIO, output: TextIO) -> None:
    output.write(str(instances(smt_file)))
