from typing import TextIO, List
import z3
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand

import argparse
import tempfile
import subprocess
import io
import sys
from pathlib import Path


def find_unsat_core() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input",
        nargs="?",
        type=argparse.FileType("r"),
        default=sys.stdin,
        help="Input SMTLIB file, defaults to stdin",
    )

    parser.add_argument(
        "output",
        nargs="?",
        type=argparse.FileType("w"),
        default=sys.stdout,
        help="Output SMTLIB file, defaults to stdout",
    )

    z3_interface = parser.add_mutually_exclusive_group(required=True)
    z3_interface.add_argument(
        "-p",
        "--programmatic",
        help="find unsat-core using Z3 programmatic API",
        action="store_true",
    )
    z3_interface.add_argument("-e", "--executable", help="Z3 executable to use")

    args = parser.parse_args()

    if args.programmatic:
        result = find_unsat_core_programmatic(args.input.read())
    else:
        result = find_unsat_core_executable(args.input, args.executable)

    args.output.write(result)


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


def find_unsat_core_executable(smt_file: TextIO, executable: str) -> str:
    parser = SmtLibParser()
    script = parser.get_script(smt_file)

    command_to_index = {id(command): i for i, command in enumerate(script.commands)}

    asserts = list(script.filter_by_command_name("assert"))
    declares = list(script.filter_by_command_name("declare-fun"))

    with tempfile.TemporaryDirectory() as tmpdir:

        def minimize_commands(commands: List[SmtLibCommand]) -> None:
            delta = 0
            for command in commands:
                script.commands.remove(command)
                path = Path(tmpdir) / "file.smt2"
                script.to_file(path, daggify=False)
                result = subprocess.run(
                    [executable, path], capture_output=True, text=True
                )

                if "unsat" not in result.stdout:
                    script.commands.insert(
                        command_to_index[id(command)] - delta, command
                    )
                else:
                    delta += 1

        minimize_commands(asserts)
        minimize_commands(declares)

    buffer = io.StringIO()

    script.serialize(buffer, daggify=False)

    return buffer.getvalue()


if __name__ == "__main__":
    find_unsat_core()
