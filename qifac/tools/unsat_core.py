import io
import shutil
import subprocess
import tempfile
from argparse import ArgumentParser, FileType, Namespace
from pathlib import Path
from typing import Optional, TextIO

import z3
from pysmt.smtlib.parser import Tokenizer

from .filter_named import filter_named
from .helpers import log_args, stdio_args
from .name import name


def find_unsat_core(args: Namespace) -> None:
    if args.programmatic:
        result = find_unsat_core_programmatic(args.input.read())
        args.output.write(result)
    else:
        find_unsat_core_executable(args.input, args.executable, args.output, args.save)


def find_unsat_core_programmatic(smt_file: str) -> str:
    solver = z3.Solver()
    solver.from_string(smt_file)

    assert solver.check() == z3.unsat

    checks = solver.assertions()
    solver.reset()
    current = list(checks)
    true = z3.BoolVal(True)
    for i in range(len(checks)):
        solver.reset()
        current[i] = true
        if solver.check(*current) != z3.unsat:
            current[i] = checks[i]

    final = [check for check in current if check is not true]

    solver.assert_exprs(*final)
    return solver.to_smt2()


def find_unsat_core_executable(
    smt_file: TextIO, executable: str, output: TextIO, save: Optional[TextIO]
) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        named_path = dir_path / "named.smt2"
        with open(input_path, "r") as input_smt, open(named_path, "w") as output_smt:
            namespace = Namespace()
            namespace.input = input_smt
            namespace.output = output_smt
            name(namespace)

        result = subprocess.run(
            [executable, named_path], capture_output=True, text=True
        ).stdout

        buffer = io.StringIO(result.splitlines()[-1])
        keep = list(Tokenizer(buffer).generator)[1:-1]

        if save is not None:
            for kept_name in keep:
                save.write(str(kept_name))
                save.write("\n")

        with open(named_path, "r") as input_smt:
            namespace = Namespace()
            namespace.input = input_smt
            namespace.output = output
            namespace.names = keep
            filter_named(namespace)


def build_parser(
    parser: ArgumentParser = ArgumentParser(),
) -> ArgumentParser:
    stdio_args(parser)
    log_args(parser)

    z3_interface = parser.add_mutually_exclusive_group(required=True)
    z3_interface.add_argument(
        "-p",
        "--programmatic",
        help="find unsat-core using Z3 programmatic API",
        action="store_true",
    )
    z3_interface.add_argument("-e", "--executable", help="Z3 executable to use")

    parser.add_argument(
        "-s",
        "--save",
        type=FileType("w"),
        help="where to save the names of unsat-core assertions",
    )

    return parser


if __name__ == "__main__":
    find_unsat_core(build_parser().parse_args())
