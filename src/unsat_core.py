import z3


def find_unsat_core() -> None:
    print("Finding unsat core")
    s = z3.Solver()
    print(s)
    pass


if __name__ == "__main__":
    find_unsat_core()
