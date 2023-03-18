import click

from .adt.cli import run_adt
from .bdd.cli import run as run_bdd


@click.group
def search() -> None:
    pass


@search.command
def hello() -> None:
    print("Hello")


search.add_command(run_adt, "adt")
search.add_command(run_bdd, "bdd")
