import click

from .adt.cli import run_adt


@click.group
def search() -> None:
    pass


@search.command
def hello() -> None:
    print("Hello")


search.add_command(run_adt, "adt")
