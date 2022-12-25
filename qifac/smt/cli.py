import shutil
import sys
from typing import List, TextIO

import click

from ..utils import smt_file_read_write
from . import (
    dedup,
    filter_names,
    keep_quantified,
    keep_quantifier_free,
    name,
    pysmt_prettify,
    skolemize,
    uglify,
    unname,
    z3_prettify,
)
from .booleanize import booleanize
from .cleaner import clean_errors, cleanup, unify_lines
from .sampler import sample


@click.group
def smt() -> None:
    pass


smt_file_read_write(smt, uglify)
smt_file_read_write(smt, unify_lines, "unfiy")
smt_file_read_write(smt, keep_quantified, "keepq")
smt_file_read_write(smt, keep_quantifier_free, "keepqf")
smt_file_read_write(smt, pysmt_prettify, "prettify")
smt_file_read_write(smt, z3_prettify)
smt_file_read_write(smt, cleanup)
smt_file_read_write(smt, dedup)
smt_file_read_write(smt, unname)
smt_file_read_write(smt, clean_errors, "clean")
smt_file_read_write(smt, booleanize, "bool")
smt_file_read_write(smt, name)
smt_file_read_write(smt, skolemize)


@smt.command(name="filter")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--names", "-n", multiple=True)
def wrap_filter_names(smt_file: TextIO, output: TextIO, names: List[str]) -> None:
    shutil.copyfileobj(filter_names(smt_file, names), output)


@smt.command(name="sample")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--instantiations", "-i", type=int)
@click.option("--quantifier-free", "-f", type=int)
def wrap_sample(
    smt_file: TextIO, output: TextIO, instantiations: int, quantifier_free: int
) -> None:
    shutil.copyfileobj(sample(smt_file, instantiations, quantifier_free), output)
