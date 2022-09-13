import shutil
import sys
from typing import Any, List, Optional, TextIO

import click
from click import Context, Parameter

from .core import find as do_find
from .core import instances as do_instances
from .instances import show as do_show
from .instances.compare import compare as do_compare
from .instances.instantiate import instantiate as do_instantiate
from .instantiation_tree import Forest
from .smt import filter_names as do_filter_names
from .smt import name as do_name
from .smt import skolemize as do_skolemize
from .smt.booleanize import booleanize as do_booleanize
from .smt.cleaner import clean_errors
from .typeinfo.parser import parse_script


class ForestType(click.ParamType):
    file: click.File

    def __init__(self) -> None:
        self.file = click.File("r")

    def convert(
        self, value: Any, param: Optional[Parameter], ctx: Optional[Context]
    ) -> Forest:
        file = self.file.convert(value, param, ctx)

        return Forest.parse_file(file)


@click.group
def run() -> None:
    pass


@run.group
def smt() -> None:
    pass


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def clean(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(clean_errors(smt_file), output)


@smt.command(name="bool")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def booleanize(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_booleanize(smt_file), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def name(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_name(smt_file), output)


@smt.command(name="filter")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--names", "-n", multiple=True)
def filter_names(smt_file: TextIO, output: TextIO, names: List[str]) -> None:
    shutil.copyfileobj(do_filter_names(smt_file, names), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def skolemize(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_skolemize(smt_file), output)


@run.group
def core() -> None:
    pass


@core.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def find(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_find(smt_file), output)


@core.command(name="instances")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def core_instances(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_instances(smt_file), output)


@run.group
def instances() -> None:
    pass


@instances.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def show(smt_file: TextIO, output: TextIO) -> None:
    output.write(str(do_show(smt_file)))


@instances.command
@click.argument("unsat_file", type=ForestType())
@click.argument("unknown_file", type=ForestType())
@click.argument("output", type=click.File("w"), default=sys.stdout)
def compare(unsat_file: Forest, unknown_file: Forest, output: TextIO) -> None:
    result = do_compare(unsat_file, unknown_file)
    for node in result:
        print(f"{node}", file=output)


@instances.command
@click.argument("smt_file", type=click.File("r"))
@click.argument("instances_file", type=ForestType())
@click.argument("output", type=click.File("w"), default=sys.stdout)
def instantiate(smt_file: TextIO, instances_file: Forest, output: TextIO) -> None:
    shutil.copyfileobj(do_instantiate(smt_file, instances_file), output)


@run.group
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
