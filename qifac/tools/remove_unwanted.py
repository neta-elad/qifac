from typing import Set, TextIO
from argparse import ArgumentParser, Namespace
from pathlib import Path


from .helpers import stdio_args


def remove_unwanted(args: Namespace) -> None:
    while line := args.input.readline():
        if "(=> true true)" not in line and "(push" not in line and "(pop" not in line:
            args.output.write(line)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    remove_unwanted(build_parser().parse_args())
