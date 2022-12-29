import click

from ..utils import smt_file_read_write
from . import count_quantifiers


@click.group
def count() -> None:
    pass


smt_file_read_write(count, count_quantifiers, "quantifiers")
