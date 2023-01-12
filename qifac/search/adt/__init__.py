from typing import List, Tuple

import z3

from .examples import many_sorted_consensus
from .models import RefModel
from .problem import Problem


def prepare_consensus() -> Tuple[List[RefModel], Problem]:
    problem, terms = many_sorted_consensus()
    print_and_check("Full query", problem.full_query())
    print_and_check("Ground query", problem.ground_query())
    z3_models = problem.generate_models(terms)
    initial_models = [RefModel(problem, i, model) for i, model in enumerate(z3_models)]
    return initial_models, problem


def print_and_check(title: str, solver: z3.Solver) -> None:
    print(f"{title}:")
    print(solver)
    print(f"=> {solver.check()}")
