from typing import TextIO, Optional, Callable
from argparse import ArgumentParser, FileType, Namespace
import sys
import io
import copy


def stdio_args(
    parser: ArgumentParser = ArgumentParser(),
) -> ArgumentParser:
    parser.add_argument(
        "input",
        nargs="?",
        type=FileType("r"),
        default=sys.stdin,
        help="Input SMTLIB file, defaults to stdin",
    )

    parser.add_argument(
        "output",
        nargs="?",
        type=FileType("w"),
        default=sys.stdout,
        help="Output SMTLIB file, defaults to stdout",
    )

    return parser


def log_args(
    parser: ArgumentParser = ArgumentParser(),
) -> ArgumentParser:
    parser.add_argument(
        "-l",
        "--log",
        nargs="?",
        type=FileType("w"),
        default=None,
        const=sys.stderr,
        help="Turn on logging of intremediate states, defaults to stderr",
    )

    return parser


def chain_stdio(args: Namespace, *funs: Callable[[Namespace], None]) -> None:
    last_output = args.input

    funs_list = list(funs)

    tail = funs_list.pop()

    for fun in funs_list:
        namespace = copy.copy(args)
        namespace.input = last_output
        last_output = namespace.output = io.StringIO()
        fun(namespace)
        last_output.seek(0)
        log_output(fun.__name__, args.log, last_output)

    namespace = copy.copy(args)
    namespace.input = last_output
    tail(namespace)


def log_output(message: str, log: Optional[TextIO], output: io.StringIO) -> None:
    if log is None:
        return

    log.write(message)
    log.write("\n")
    log.write("-" * len(message))
    log.write("\n")
    log.write(output.getvalue())
    log.write("-" * len(message))
    log.write("\n")
