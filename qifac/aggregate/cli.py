import shutil
import sys
from pathlib import Path
from typing import TextIO

import click

from . import aggregate_all, aggregate_categories, aggregate_qids


@click.group
def aggregate() -> None:
    pass


@aggregate.command(name="qids")
@click.argument(
    "analysis_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_aggregate_qids(analysis_dir: Path, output: TextIO) -> None:
    shutil.copyfileobj(aggregate_qids(analysis_dir), output)


@aggregate.command(name="categories")
@click.argument(
    "analysis_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def wrap_aggregate_categories(analysis_dir: Path, output: TextIO) -> None:
    shutil.copyfileobj(aggregate_categories(analysis_dir), output)


@aggregate.command(name="all")
@click.argument(
    "analysis_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "aggregate_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def wrap_aggregate_all(analysis_dir: Path, aggregate_dir: Path) -> None:
    aggregate_all(analysis_dir, aggregate_dir)
