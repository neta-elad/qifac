from typing import Mapping, Set, TextIO, Tuple

import z3


def get_model_size(smt_file: TextIO, debug: bool = False) -> Tuple[int, int]:
    solver = z3.Solver()
    smt_file_string = smt_file.read()
    solver.from_string(smt_file_string)

    rest_smt = remove_sort_declarations(smt_file_string)

    assert solver.check() == z3.sat

    sorts = get_sorts(solver)

    unconstrained_model = solver.model()

    max_size = 1

    for sort in sorts:
        sort_size = len(unconstrained_model.get_universe(sort))
        if sort_size > max_size:
            max_size = sort_size

    if debug:
        print(f"Got sat for {max_size}")

    lower_bound = 1
    strict_upper_bound = upper_bound = max_size

    while lower_bound < upper_bound:
        check_size = (lower_bound + upper_bound) // 2
        # check_size = lower_bound + 1

        # solver = constrain(smt_file_string, sorts, check_size)
        solver = constrain_with_enum(rest_smt, sorts, check_size)

        result = solver.check()

        if debug:
            print(f"Got {result} for {check_size}")

        if result == z3.sat:
            strict_upper_bound = upper_bound = check_size
        elif result == z3.unsat:
            lower_bound = check_size + 1
        else:
            if debug:
                print(f"Reason: {solver.reason_unknown()}")
            upper_bound = check_size
            if check_size - 1 == lower_bound:
                if debug:
                    print(f"Lower bound {lower_bound} ({max_size})")
                break

    return lower_bound, strict_upper_bound


def constrain(smt_file: str, sorts: Set[z3.SortRef], size: int) -> z3.Solver:
    solver = z3.Solver()
    solver.from_string(smt_file)
    for sort in sorts:
        solver.add(sort_size_constraint(sort, size))
        # solver.add(sort_size_constraint_no_constants(sort, size))

    return solver


def print_sizes(solver: z3.Solver) -> None:
    for sort, size in get_model_sizes(solver).items():
        print(f"|{sort}| = {size}")


def get_model_sizes(solver: z3.Solver) -> Mapping[z3.SortRef, int]:
    assert solver.check() == z3.sat
    model = solver.model()
    return {sort: len(model.get_universe(sort)) for sort in model.sorts()}


def get_sorts(solver: z3.Solver) -> Set[z3.SortRef]:
    assert solver.check() == z3.sat
    return set(solver.model().sorts())


def sort_size_constraint(sort: z3.SortRef, size: int) -> z3.BoolRef:
    constants = [z3.Const(f"{sort}!size!{i}", sort) for i in range(size)]
    x = z3.Const(f"{sort}!size!x", sort)

    return z3.And(
        z3.Distinct(*constants), z3.ForAll(x, z3.Or(*[x == c for c in constants]))
    )


def sort_size_constraint_no_constants(sort: z3.SortRef, size: int) -> z3.BoolRef:
    variables = [z3.Const(f"{sort}!size!{i}", sort) for i in range(size + 1)]

    clauses = set()
    for x in variables:
        for y in variables:
            if x.eq(y):
                break

            clauses.add(x == y)

    return z3.ForAll(variables, z3.Or(*clauses))


def remove_sort_declarations(smt_file_string: str) -> str:
    rest = []
    for line in smt_file_string.splitlines():
        if not line.strip().startswith("(declare-sort"):
            rest.append(line)

    return "\n".join(rest)


def constrain_with_enum(smt_file: str, sorts: Set[z3.SortRef], size: int) -> z3.Solver:
    smt_file_with_declarations = []
    for sort in sorts:
        smt_file_with_declarations.append(sort_enum_constraint(sort, size))

    smt_file_with_declarations.append(smt_file)

    solver = z3.Solver()
    solver.set("timeout", 5 * 1000)
    solver.from_string("\n".join(smt_file_with_declarations))

    return solver


def sort_enum_constraint(sort: z3.SortRef, size: int) -> str:
    constants = " ".join(f"({sort}{i})" for i in range(size))
    return f"(declare-datatypes (({sort} 0)) (({constants})))"
