from dataclasses import dataclass
from functools import cached_property
from itertools import product
from typing import Iterable, List, Mapping, Tuple

import z3

from .problem import Problem
from .utils import cast_bool, to_bool


@dataclass
class Model:
    problem: Problem
    id: int
    ref: z3.ModelRef

    @cached_property
    def universe(self) -> List[z3.ExprRef]:
        return sorted(
            self.ref.get_universe(self.problem.sort),
            key=lambda x: int(str(x).split("!")[-1]),
        )

    @cached_property
    def sort_and_elements(self) -> Tuple[z3.SortRef, List[z3.Const]]:
        return z3.EnumSort(
            f"E_{self.id}",
            [f"E_{self.id}_{i}" for i in range(len(self.universe))],
            ctx=self.problem.context,
        )

    @cached_property
    def sort(self) -> z3.SortRef:
        return self.sort_and_elements[0]

    @cached_property
    def elements(self) -> List[z3.Const]:
        return self.sort_and_elements[1]

    @cached_property
    def constant_interpretations(self) -> List[int]:
        return [
            self.universe.index(self.ref.eval(c, model_completion=True))
            for c in self.problem.constants
        ]

    @cached_property
    def function_interpretations(self) -> List[Mapping[Tuple[int, ...], int]]:
        return [
            {
                xs: self.universe.index(
                    self.ref.eval(
                        fun(*(self.universe[x] for x in xs)), model_completion=True
                    )
                )
                for xs in product(range(len(self.universe)), repeat=fun.arity())
            }
            for fun in self.problem.functions
        ]

    @cached_property
    def interpret(self) -> z3.FuncDeclRef:
        t = z3.Const("t", self.problem.ground_term_adt)
        interpret = z3.RecFunction(
            f"interpret_{self.id}", self.problem.ground_term_adt, self.sort
        )
        entries = []
        for c, ci in zip(self.problem.constants, self.constant_interpretations):
            entries.append(
                (
                    getattr(self.problem.ground_term_adt, f"is_GT_{c}")(t),
                    self.elements[ci],
                )
            )
        for f, fi in zip(self.problem.functions, self.function_interpretations):
            for xs in product(range(len(self.universe)), repeat=f.arity()):
                entries.append(
                    (
                        z3.And(
                            getattr(self.problem.ground_term_adt, f"is_GT_{f}")(t),
                            *(
                                interpret(
                                    getattr(
                                        self.problem.ground_term_adt, f"GT_{f}_{i}"
                                    )(t)
                                )
                                == self.elements[xs[i]]
                                for i in range(f.arity())
                            ),
                        ),
                        self.elements[fi[xs]],
                    )
                )

        definition = self.elements[0]
        for condition, if_true in reversed(entries):
            definition = z3.If(condition, if_true, definition)
        z3.RecAddDefinition(interpret, t, definition)

        return interpret

    @cached_property
    def interpret_instantiation(self) -> z3.FuncDeclRef:
        t = z3.Const("t", self.problem.instantiation_adt)
        interpret_inst = z3.RecFunction(
            f"interpret_inst_{self.id}",
            self.problem.instantiation_adt,
            z3.BoolSort(ctx=self.problem.context),
        )

        entries = []

        for qid, quantifier in enumerate(self.problem.forall_assertions):
            for xs in product(range(len(self.universe)), repeat=quantifier.num_vars()):
                entries.append(
                    (
                        z3.And(
                            getattr(self.problem.instantiation_adt, f"is_Inst_{qid}")(
                                t
                            ),
                            *(
                                self.interpret(
                                    getattr(
                                        self.problem.instantiation_adt,
                                        f"Inst_{qid}_{i}",
                                    )(t)
                                )
                                == self.elements[xs[i]]
                                for i in range(quantifier.num_vars())
                            ),
                        ),
                        cast_bool(self.bodies[qid](*(self.elements[x] for x in xs))),
                    )
                )

        definition = z3.BoolVal(True, ctx=self.problem.context)

        for condition, if_true in reversed(entries):
            definition = z3.If(condition, if_true, definition)
        z3.RecAddDefinition(interpret_inst, t, definition)

        return interpret_inst

    @cached_property
    def bodies(self) -> List[z3.FuncDeclRef]:
        return [
            z3.Function(
                f"body_{self.id}_{i}",
                *([self.sort] * f.num_vars() + [z3.BoolSort(ctx=self.problem.context)]),
            )
            for i, f in enumerate(self.problem.forall_assertions)
        ]

    @cached_property
    def indicators(self) -> List[z3.BoolRef]:
        return [
            z3.Bool(f"violate_{self.id}_{i}", ctx=self.problem.context)
            for i in range(len(self.problem.forall_assertions))
        ]

    @cached_property
    def witnesses(self) -> List[List[z3.Const]]:
        return [
            [
                z3.Const(f"witness_{self.id}_{i}_{j}", self.sort)
                for j in range(quantifier.num_vars())
            ]
            for i, quantifier in enumerate(self.problem.forall_assertions)
        ]

    def add_bodies(self, solver: z3.Solver) -> None:
        for quantifier, body in zip(self.problem.forall_assertions, self.bodies):
            num_vars = quantifier.num_vars()
            for xs, es in zip(
                product(self.universe, repeat=num_vars),
                product(self.elements, repeat=num_vars),
            ):
                res = to_bool(
                    self.ref.eval(
                        z3.substitute_vars(quantifier.body(), *xs),
                        model_completion=True,
                    )
                )
                literal = cast_bool(body(*es))
                if not res:
                    literal = z3.Not(literal)
                solver.add(literal)

    def add_indicators(self, solver: z3.Solver) -> None:
        solver.add(z3.Or(*self.indicators))

    def add_witnesses(self, solver: z3.Solver, terms: Iterable[z3.ExprRef]) -> None:
        for i in range(len(self.problem.forall_assertions)):
            solver.add(
                z3.Implies(
                    self.indicators[i],
                    z3.Not(cast_bool(self.bodies[i](*self.witnesses[i]))),
                )
            )
            for w in self.witnesses[i]:
                solver.add(
                    z3.Implies(
                        self.indicators[i],
                        z3.Or(*(w == self.interpret(t) for t in terms)),
                    )
                )

    def add_instantiations(
        self, solver: z3.Solver, instantiations: Iterable[z3.ExprRef]
    ) -> None:
        self.add_bodies(solver)

        solver.add(
            z3.Or(
                *(
                    z3.Not(cast_bool(self.interpret_instantiation(instantiation)))
                    for instantiation in instantiations
                )
            )
        )

    def add(self, solver: z3.Solver, terms: Iterable[z3.ExprRef]) -> None:
        self.add_bodies(solver)
        self.add_indicators(solver)
        self.add_witnesses(solver, terms)
