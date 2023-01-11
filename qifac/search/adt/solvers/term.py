from dataclasses import dataclass, field
from functools import cached_property
from typing import List

import z3

from ..models import RefModel
from ..problem import Problem
from ..utils import to_bool


@dataclass
class TermSolver:
    problem: Problem
    initial_models: List[RefModel]
    n_terms: int = field(default=5)

    def __post_init__(self) -> None:
        print(f"\nTrying to do MBQI:\n")
        self.solve()
        print(f"ADT-based MBQI done! (problem_solver is {self.problem_solver.check()})")

    @cached_property
    def terms_for_instantiation(self) -> List[z3.Const]:
        return [
            z3.Const(f"t_{sort}_{i}", self.problem.ground_term_adts[sort])
            for i in range(self.n_terms)
            for sort in self.problem.sorts
        ]

    @cached_property
    def adt_solver(self) -> z3.Solver:
        solver = z3.Solver(ctx=self.problem.context)
        for model in self.initial_models:
            model.add(solver, self.terms_for_instantiation)

        return solver

    @cached_property
    def models(self) -> List[RefModel]:
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
        new_model = RefModel(self.problem, new_id, new_ref)
        self.models.append(new_model)
        new_model.add(self.adt_solver, self.terms_for_instantiation)

        return new_id

    def get_instantiation(
        self, new_adt_model: z3.ModelRef, model: RefModel
    ) -> z3.BoolRef:
        print(f"model {model.id}:")
        violated = [
            new_adt_model[v] is not None and to_bool(new_adt_model[v])
            for v in model.indicators
        ]
        assert any(violated)
        assert violated.count(True) == 1
        for i, v in enumerate(violated):
            if not v:
                continue
            print(
                f"    violates assertion {i}: {self.problem.quantified_assertions[i]}"
            )
            ws = [new_adt_model[w] for w in model.witnesses[i]]
            print(f"    witnesses are: {ws}")
            adts = []
            for w in ws:
                eqs = [
                    to_bool(
                        z3.simplify(
                            w == new_adt_model.eval(model.interpret_any(new_adt_model[t]))
                        )
                    )
                    for t in self.terms_for_instantiation
                ]
                assert any(eqs)
                j = eqs.index(True)
                adts.append(new_adt_model[self.terms_for_instantiation[j]])
            print(f"    ground term ADTs are: {adts}")
            ts = [self.problem.adt_to_term(t) for t in adts]
            print(f"    ground terms are: {ts}")
            elems = [model.ref.eval(t) for t in ts]
            print(f"    ground terms evaluate to: {elems}")
            assert [model.universe.index(e) for e in elems] == [
                model.elements.index(new_adt_model[w]) for w in model.witnesses[i]
            ]
            instantiation = self.problem.quantified_assertions[i].instantiate(*ts)

            print(f"    ground instance is: {instantiation}")
            print(f"    it evaluates to: {model.ref.eval(instantiation)}")
            assert z3.is_false(model.ref.eval(instantiation)), (
                model.id,
                ws,
                adts,
                ts,
                elems,
                instantiation,
                model.ref.eval(instantiation),
            )
            # only the first violated in each model
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
                print(f"Cannot hit all models with {self.n_terms} ground terms")
                break
            else:
                assert False

            print(f"\nSummary for the {new_id + 1}-th iteration:")
            print(
                f"\nFound the following ADTs:",
                [new_adt_model[t] for t in self.terms_for_instantiation],
            )
            print(
                f"\nThey correspond to terms:",
                [
                    self.problem.adt_to_term(new_adt_model[t])
                    for t in self.terms_for_instantiation
                ],
            )
            print(
                f"\nAll models are hit using the following {len(ground_instantiations)} ground instantiations:"
            )
            for g in ground_instantiations:
                print(f"\n{g}")
                self.problem_solver.add(g)
