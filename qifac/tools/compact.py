from argparse import ArgumentParser, FileType, Namespace

from pysmt.smtlib.parser import SmtLibParser

from .helpers import stdio_args


def run(args: Namespace) -> None:
    smt_parser = SmtLibParser()

    core = smt_parser.get_script(args.core)
    source = smt_parser.get_script(args.source)
    script = smt_parser.get_script(args.input)

    if args.uglify is not None:
        script.serialize(args.uglify, daggify=False)

    core_asserts = list(core.filter_by_command_name("assert"))
    source_asserts = list(source.filter_by_command_name("assert"))
    asserts = list(script.filter_by_command_name("assert"))

    for command in asserts:
        if command in source_asserts and command not in core_asserts:
            script.commands.remove(command)

    script.serialize(args.output, daggify=False)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    parser.add_argument(
        "-c",
        "--core",
        type=FileType("r"),
        help="Instantiated core",
    )
    parser.add_argument(
        "-s",
        "--source",
        required=True,
        type=FileType("r"),
        help="Source of instantiated core",
    )
    parser.add_argument(
        "-u",
        "--uglify",
        required=True,
        type=FileType("w"),
        help="Uglify input",
    )
    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
