import click

from . import prepare_consensus
from .solvers.instantiation import InstantiationSolver
from .solvers.term import TermSolver


@click.group
def run_adt() -> None:
    pass


@run_adt.command
def terms() -> None:
    print("Running ADT search process using terms solver")
    initial_models, problem = prepare_consensus()

    TermSolver(problem, initial_models)


@run_adt.command
def insts() -> None:
    print("Running ADT search process using instantiations solver")
    initial_models, problem = prepare_consensus()

    InstantiationSolver(problem, initial_models)
