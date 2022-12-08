import click

from .adt import run_adt


@click.group
def search() -> None:
    pass


@search.command
def hello() -> None:
    print("Hello")


@search.command
def adt() -> None:
    run_adt()
