import click

from .instances import instances
from .typeinfo import typeinfo


@click.group
def run() -> None:
    pass


run.add_command(instances)
run.add_command(typeinfo)
