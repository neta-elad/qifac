import shutil
import sys
from typing import TextIO

import click

from ..cli_types import ForestType
from ..parsing.instantiation_tree import Forest
from . import count_qids, flatten, show, simple_instances
from .compare import compare
from .instantiate import instantiate


@click.group
def instances() -> None:
    pass


@instances.command("show")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--proof/--no-proof", default=True)
def wrap_show(smt_file: TextIO, output: TextIO, proof: bool) -> None:
    output.write(str(show(smt_file, with_proof=proof)))


@instances.command("simple")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_simple_instances(smt_file: TextIO, output: TextIO) -> None:
    output.write(simple_instances(smt_file))


@instances.command
@click.argument("instances_file", type=ForestType(), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def qids(instances_file: Forest, output: TextIO) -> None:
    for qid, count in count_qids(instances_file):
        print(f"{qid} {count}", file=output)


@instances.command(name="flatten")
@click.argument("instances_file", type=ForestType(), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_flatten(instances_file: Forest, output: TextIO) -> None:
    for flat in flatten(instances_file):
        print(f"{flat}", file=output)


@instances.command("compare")
@click.argument("unsat_file", type=ForestType())
@click.argument("unknown_file", type=ForestType())
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_compare(unsat_file: Forest, unknown_file: Forest, output: TextIO) -> None:
    result = compare(unsat_file, unknown_file)
    for node in result:
        print(f"{node}", file=output)


@instances.command("instantiate")
@click.argument("smt_file", type=click.File("r"))
@click.argument("instances_file", type=ForestType())
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_instantiate(smt_file: TextIO, instances_file: Forest, output: TextIO) -> None:
    shutil.copyfileobj(instantiate(smt_file, instances_file), output)


@instances.command
@click.argument("smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--proof/--no-proof", default=True)
def auto(smt_file: TextIO, output: TextIO, proof: bool) -> None:
    forest = show(smt_file, with_proof=proof)
    smt_file.seek(0)
    shutil.copyfileobj(instantiate(smt_file, forest), output)
