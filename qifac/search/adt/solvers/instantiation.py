from dataclasses import dataclass, field
from functools import cached_property
from typing import List

import z3

from ..model import Model
from ..problem import Problem
from ..utils import to_bool


@dataclass
class InstantiationSolver:
    problem: Problem
    initial_models: List[Model]
    n_instantiations: int = field(default=5)

    def __post_init__(self) -> None:
        print(f"\nTrying to do MBQI:\n")
        self.solve()
        print(f"ADT-based MBQI done! (problem_solver is {self.problem_solver.check()})")

    @cached_property
    def instantiations(self) -> List[z3.Const]:
        return [
            z3.Const(f"i_{i}", self.problem.instantiation_adt)
            for i in range(self.n_instantiations)
        ]

    @cached_property
    def adt_solver(self) -> z3.Solver:
        solver = z3.Solver(ctx=self.problem.context)
        for model in self.initial_models:
            model.add_instantiations(solver, self.instantiations)

        return solver

    @cached_property
    def models(self) -> List[Model]:
        return list(self.initial_models)

    @cached_property
    def problem_solver(self) -> z3.Solver:
        solver = z3.Solver()
        solver.add(*self.problem.qf_assertions)
        return solver

    def add_new_model(self) -> int:
        size, new_ref = self.problem.minimize_model(self.problem_solver)
        new_id = len(self.models)
        print(f"\nFound {new_id + 1}-th model with {size} elements: \n{new_ref}")
        new_model = Model(self.problem, new_id, new_ref)
        self.models.append(new_model)
        new_model.add_instantiations(self.adt_solver, self.instantiations)

        return new_id

    def get_instantiation(self, new_adt_model: z3.ModelRef, model: Model) -> z3.BoolRef:
        print(f"model {model.id}:")

        violated = {
            self.problem.adt_to_instantiation(inst): model.ref.eval(
                self.problem.adt_to_instantiation(inst)
            )
            for inst in [new_adt_model[inst_var] for inst_var in self.instantiations]
            if inst is not None
        }
        for instantiation, evaluation in violated.items():
            print(f"    ground instance is: {instantiation}")
            print(f"    it evaluates to: {evaluation}")
            if not to_bool(evaluation):
                return instantiation

        raise RuntimeError(f"Model {model.id} violated no instantiation")

    def solve(self) -> None:
        while (result := self.problem_solver.check()) != z3.unsat:
            assert result == z3.sat
            new_id = self.add_new_model()
            result = self.adt_solver.check()
            print(f"finding new instantiations: {result}")
            ground_instantiations: List[z3.BoolRef] = []
            if result == z3.sat:
                new_adt_model = self.adt_solver.model()
                for model in self.models:
                    ground_instantiations.append(
                        self.get_instantiation(new_adt_model, model)
                    )
            elif result == z3.unsat:
                print(
                    f"Cannot hit all models with {self.instantiations} instantiations"
                )
                break
            else:
                assert False

            print(f"\nSummary for the {new_id + 1}-th iteration:")
            print(
                f"\nFound the following ADTs:",
                [new_adt_model[i] for i in self.instantiations],
            )
            print(
                f"\nThey correspond to terms:",
                [
                    self.problem.adt_to_instantiation(new_adt_model[i])
                    for i in self.instantiations
                ],
            )
            print(
                f"\nAll models are hit using the following {len(ground_instantiations)} ground instantiations:"
            )
            for g in ground_instantiations:
                print(f"\n{g}")
                self.problem_solver.add(g)
