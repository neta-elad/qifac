from argparse import ArgumentParser, Namespace

from .helpers import stdio_args


def remove_unwanted(args: Namespace) -> None:
    saw_checksat = False
    while line := args.input.readline():
        if saw_checksat:
            continue
        if line.startswith("(push") or line.startswith("(pop"):
            continue
        if "(=> true true" in line:
            continue
        args.output.write(line)

        if line.startswith("(check-sat"):
            saw_checksat = True


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    remove_unwanted(build_parser().parse_args())
