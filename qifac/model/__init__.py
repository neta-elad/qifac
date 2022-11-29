from itertools import product
from typing import TextIO, Mapping, Set

import z3


def get_model_size(smt_file: TextIO) -> int:
    solver = z3.Solver()
    solver.from_string(smt_file.read())

    assert solver.check() == z3.sat

    sorts = get_sorts(solver)

    unconstrained_model = solver.model()

    max_size = 1

    for sort in sorts:
        sort_size = len(unconstrained_model.get_universe(sort))
        if sort_size > max_size:
            max_size = sort_size

    size = 1

    lower_bound = 1
    upper_bound = max_size

    solver.push()

    while lower_bound < upper_bound:
        check_size = (lower_bound + upper_bound) // 2

        constrain(solver, sorts, check_size)

        result = solver.check()

        if result == z3.sat:
            if check_size == lower_bound:
                print(f"Found {check_size}")
                break
            upper_bound = check_size
        elif result == z3.unsat:
            lower_bound = check_size
        elif check_size - 1 == lower_bound:
            print(f"Lower bound {lower_bound}")
            break
        else:
            upper_bound = check_size

    return lower_bound

def constrain(solver: z3.Solver, sorts: Set[z3.SortRef], size: int) -> None:
    solver.pop()
    solver.push()
    for sort in sorts:
        solver.add(sort_size_constraint(sort, size))



def print_sizes(solver: z3.Solver) -> None:
    for sort, size in get_model_sizes(solver).items():
        print(f"|{sort}| = {size}")

def get_model_sizes(solver: z3.Solver) -> Mapping[z3.SortRef, int]:
    assert solver.check() == z3.sat
    model = solver.model()
    return {model.get_sort(i): model.get_universe(model.get_sort(i)) for i in range(model.num_sorts())}


def get_sorts(solver: z3.Solver) -> Set[z3.SortRef]:
    assert solver.check() == z3.sat
    model = solver.model()
    return {model.get_sort(i) for i in range(model.num_sorts())}


def sort_size_constraint(sort: z3.SortRef, size: int) -> z3.BoolRef:
    variables = [z3.Const(f"Size{i}", sort) for i in range(size + 1)]

    clauses = set()

    for x in variables:
        for y in variables:
            if x.eq(y):
                break
            clauses.add(x == y)

    return z3.ForAll(variables, z3.Or(*clauses))