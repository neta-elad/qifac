import z3

from .examples import consensus
from .models import RefModel
from .solvers.instantiation import InstantiationSolver


def run_adt() -> None:
    print("Running ADT search process")
    problem, terms = consensus()
    print_and_check("Full query", problem.full_query())
    print_and_check("Ground query", problem.ground_query())

    z3_models = problem.generate_models(terms)

    initial_models = [RefModel(problem, i, model) for i, model in enumerate(z3_models)]

    # TermSolver(problem, initial_models)

    InstantiationSolver(problem, initial_models)


def print_and_check(title: str, solver: z3.Solver) -> None:
    print(f"{title}:")
    print(solver)
    print(f"=> {solver.check()}")
