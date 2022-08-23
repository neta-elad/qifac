from ast import parse
from typing import Set, Dict, Any, TextIO
from argparse import ArgumentParser, Namespace, FileType
import sys
import io

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter
from pysmt.fnode import FNode

from .helpers import stdio_args


def run(args: Namespace) -> None:
    left_lines = assert_formulas(args.left)
    right_lines = assert_formulas(args.right)

    if left_lines == right_lines:
        print("Equal")
    elif left_lines.issubset(right_lines):
        print("Left is subset of right")
    elif right_lines.issubset(left_lines):
        print("Right is subset of left")
    else:
        intersection = left_lines.intersection(right_lines)
        print(
            f"Intersection has {len(intersection)} asserts ({len(left_lines)}, {len(right_lines)})"
        )

        print("Right has the following exclusive asserts:")
        buffer = io.StringIO()
        printer = SmtPrinter(buffer)
        for line in right_lines.difference(left_lines):
            printer.printer(line)
            buffer.write("\n\n")

        print(buffer.getvalue())


def assert_formulas(script: TextIO) -> Set[FNode]:
    return {
        command.args[0]
        for command in SmtLibParser()
        .get_script(script)
        .filter_by_command_name("assert")
    }


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser.add_argument(
        "left",
        type=FileType("r"),
        help="Input left to compare",
    )

    parser.add_argument(
        "right",
        nargs="?",
        type=FileType("r"),
        default=sys.stdin,
        help="Input right to compare",
    )

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
