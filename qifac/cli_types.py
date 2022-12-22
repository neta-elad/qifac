from typing import Any, Optional

import click
from click import Parameter, Context

from qifac.parsing.instantiation_tree import Forest


class ForestType(click.ParamType):
    file: click.File

    def __init__(self) -> None:
        self.file = click.File("r")

    def convert(
        self, value: Any, param: Optional[Parameter], ctx: Optional[Context]
    ) -> Forest:
        file = self.file.convert(value, param, ctx)

        return Forest.parse_file(file)
