from argparse import ArgumentParser, Namespace

from .helpers import stdio_args


def run(args: Namespace) -> None:
    while line := args.input.readline():
        stripped = line.rstrip()
        if line.startswith("("):
            args.output.write("\n")
        args.output.write(stripped)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
