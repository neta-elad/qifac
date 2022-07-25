import z3

import argparse


def find_unsat_core() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", help="SMTLIB file to find unsat-core")
    parser.add_argument(
        "-p",
        "--programmatic",
        help="find unsat-core using Z3 programmatic API",
        action="store_true",
    )

    args = parser.parse_args()

    print(f"Reading SMTLIB file {args.filename}")

    if args.programmatic:
        find_unsat_core_programmatic(args.filename)


def find_unsat_core_programmatic(filename: str) -> None:
    solver = z3.Solver()
    solver.from_file(filename)

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
    print(solver.to_smt2())


if __name__ == "__main__":
    find_unsat_core()
