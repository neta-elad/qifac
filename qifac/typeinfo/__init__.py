from typing import TextIO

import click

from .parser import TypeInfo, parse_script


@click.group
def typeinfo() -> None:
    pass


@typeinfo.command
@click.argument("smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), required=False, default=None)
def parse(smt_file: TextIO, output: TextIO) -> TypeInfo:
    type_info = parse_script(smt_file)

    if output is not None:
        for ground in type_info.grounds:
            kind = type_info.get_type(ground)

            if kind is not None:
                output.write(f"{ground}: {kind}\n")

    return type_info
