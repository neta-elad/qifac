from dataclasses import dataclass
from functools import cached_property
from itertools import product
from typing import Dict, Iterable, List, Mapping, Tuple, TypeVar, cast

import z3

from .problem import Problem
from .utils import Relation, cast_bool, cast_relation, to_bool

AnyExprRef = TypeVar("AnyExprRef", bound=z3.ExprRef)


@dataclass
class RefModel:
    problem: Problem
    id: int
    ref: z3.ModelRef

    @cached_property
    def sort_universe(self) -> Dict[z3.SortRef, List[z3.ExprRef]]:
        return {
            sort: sorted(
                self.ref.get_universe(sort),
                key=lambda x: int(str(x).split("!")[-1]),
            )
            for sort in self.problem.sorts
        }

    @cached_property
    def universe(self) -> List[z3.ExprRef]:
        return self.sort_universe[self.problem.sort]

    @cached_property
    def sorts_and_elements(self) -> Dict[z3.SortRef, Tuple[z3.SortRef, List[z3.Const]]]:
        return {
            sort: z3.EnumSort(
                f"{sort}_E_{self.id}",
                [
                    f"{sort}_E_{self.id}_{i}"
                    for i in range(len(self.sort_universe[sort]))
                ],
                ctx=self.problem.context,
            )
            for sort in self.problem.sorts
        }

    @cached_property
    def sorts(self) -> Dict[z3.SortRef, z3.SortRef]:
        return {sort: self.sorts_and_elements[sort][0] for sort in self.problem.sorts}

    @cached_property
    def sort_elements(self) -> Dict[z3.SortRef, List[z3.Const]]:
        return {sort: self.sorts_and_elements[sort][1] for sort in self.problem.sorts}

    @cached_property
    def sort(self) -> z3.SortRef:
        return self.sorts[self.problem.sort]

    @cached_property
    def elements(self) -> List[z3.Const]:
        return self.sort_elements[self.problem.sort]

    @cached_property
    def sort_constant_interpretations(self) -> Dict[z3.SortRef, List[int]]:
        return {
            sort: [
                self.sort_universe[sort].index(self.ref.eval(c, model_completion=True))
                for c in self.problem.sort_constants[sort]
            ]
            for sort in self.problem.sorts
        }

    @cached_property
    def constant_interpretations(self) -> List[int]:
        return self.sort_constant_interpretations[self.problem.sort]

    @cached_property
    def sort_function_interpretations(
        self,
    ) -> Dict[z3.SortRef, List[Mapping[Tuple[int, ...], int]]]:
        return {
            sort: [
                {
                    xs: self.sort_universe[sort].index(
                        self.ref.eval(
                            fun(
                                *(
                                    self.sort_universe[fun.domain(i)][x]
                                    for i, x in enumerate(xs)
                                )
                            ),
                            model_completion=True,
                        )
                    )
                    for xs in product(
                        *[
                            range(len(self.sort_universe[fun.domain(i)]))
                            for i in range(fun.arity())
                        ]
                    )
                }
                for fun in self.problem.sort_functions[sort]
            ]
            for sort in self.problem.sorts
        }

    @cached_property
    def function_interpretations(self) -> List[Mapping[Tuple[int, ...], int]]:
        return self.sort_function_interpretations[self.problem.sort]

    @cached_property
    def interpret(self) -> z3.FuncDeclRef:
        return self.sort_interpret[self.problem.sort]

    def interpret_any(self, term: z3.ExprRef) -> z3.ExprRef:
        return self.sort_interpret[self.problem.ground_term_adts_to_sort[term.decl().range()]](term)

    @cached_property
    def sort_interpret(self) -> Dict[z3.SortRef, z3.FuncDeclRef]:
        ts = {
            sort: z3.Const("t", self.problem.ground_term_adts[sort])
            for sort in self.problem.sorts
        }
        interprets = {
            sort: z3.RecFunction(
                f"{sort}_interpret_{self.id}",
                self.problem.ground_term_adts[sort],
                self.sorts[sort],
            )
            for sort in self.problem.sorts
        }

        for sort in self.problem.sorts:
            interpret = interprets[sort]
            t = ts[sort]
            entries = []
            for c, ci in zip(
                self.problem.sort_constants[sort], self.constant_interpretations
            ):
                entries.append(
                    (
                        getattr(self.problem.ground_term_adts[sort], f"is_{sort}_GT_{c}")(t),
                        self.elements[ci],
                    )
                )
            for f, fi in zip(
                self.problem.sort_functions[sort],
                self.sort_function_interpretations[sort],
            ):
                for xs in product(
                    *[
                        range(len(self.sort_universe[f.domain(i)]))
                        for i in range(f.arity())
                    ]
                ):
                    entries.append(
                        (
                            z3.And(
                                getattr(
                                    self.problem.ground_term_adts[sort],
                                    f"is_{sort}_GT_{f}",
                                )(t),
                                *(
                                    interpret(
                                        getattr(
                                            self.problem.ground_term_adts[sort],
                                            f"{sort}_GT_{f}_{i}",
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

        return cast(Dict[z3.SortRef, z3.FuncDeclRef], interprets)

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
                *([self.sort] * f.num_vars + [z3.BoolSort(ctx=self.problem.context)]),
            )
            for i, f in enumerate(self.problem.quantified_assertions)
        ]

    @cached_property
    def indicators(self) -> List[z3.BoolRef]:
        return [
            z3.Bool(f"violate_{self.id}_{i}", ctx=self.problem.context)
            for i in range(len(self.problem.quantified_assertions))
        ]

    @cached_property
    def witnesses(self) -> List[List[z3.Const]]:
        return [
            [
                z3.Const(f"witness_{self.id}_{i}_{j}", self.sort)
                for j in range(quantifier.num_vars)
            ]
            for i, quantifier in enumerate(self.problem.quantified_assertions)
        ]

    def add_bodies(self, solver: z3.Solver) -> None:
        for quantifier, body in zip(self.problem.quantified_assertions, self.bodies):
            num_vars = quantifier.num_vars
            for xs, es in zip(
                product(self.universe, repeat=num_vars),
                product(self.elements, repeat=num_vars),
            ):
                res = to_bool(
                    self.ref.eval(
                        quantifier.instantiate(*xs),
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
        for i in range(len(self.problem.quantified_assertions)):
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
                        z3.Or(*(w == self.interpret_any(t) for t in terms)),
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


@dataclass
class SizedModel:
    problem: Problem
    id: int
    size: int

    @cached_property
    def sort_and_elements(self) -> Tuple[z3.SortRef, List[z3.Const]]:
        return z3.EnumSort(
            f"E_{self.id}",
            [f"E_{self.id}_{i}" for i in range(self.size)],
            ctx=self.problem.context,
        )

    @cached_property
    def sort(self) -> z3.SortRef:
        return self.sort_and_elements[0]

    @cached_property
    def elements(self) -> List[z3.Const]:
        return self.sort_and_elements[1]

    @cached_property
    def constants(self) -> Mapping[z3.Const, z3.Const]:
        return {
            c: z3.Const(f"c_{self.id}_{c}", self.sort)
            for c in self.problem.sort_constants[self.problem.sort]
        }

    @cached_property
    def functions(self) -> Dict[z3.FuncDeclRef, z3.FuncDeclRef]:
        return {
            f: z3.Function(f"f_{self.id}_{f}", *([self.sort] * (1 + f.arity())))
            for f in self.problem.functions
        }

    @cached_property
    def relations(self) -> Dict[Relation, Relation]:
        return {
            r: cast_relation(
                z3.Function(
                    f"R_{self.id}_{r}",
                    *([self.sort] * r.arity() + [z3.BoolSort(self.problem.context)]),
                )
            )
            for r in self.problem.relations
        }

    @cached_property
    def applications(self) -> Mapping[z3.FuncDeclRef, z3.FuncDeclRef]:
        return self.functions | self.relations

    @cached_property
    def interpret(self) -> z3.FuncDeclRef:
        t = z3.Const("t", self.problem.ground_term_adt)
        interpret = z3.RecFunction(
            f"interpret_{self.id}", self.problem.ground_term_adt, self.sort
        )
        entries = []
        for c, ci in self.constants.items():
            entries.append(
                (
                    getattr(self.problem.ground_term_adt, f"is_GT_{c}")(t),
                    cast(z3.ExprRef, ci),
                )
            )
        for f, fi in self.functions.items():
            for es in product(self.elements, repeat=f.arity()):
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
                                == es[i]
                                for i in range(f.arity())
                            ),
                        ),
                        fi(*es),
                    )
                )

        definition = cast(z3.ExprRef, self.elements[0])
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
            for es in product(self.elements, repeat=quantifier.num_vars()):
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
                                == es[i]
                                for i in range(quantifier.num_vars())
                            ),
                        ),
                        cast_bool(
                            self.eval(quantifier.body(), list(reversed(es)))
                        ),  # quantifier vars in reverse order
                    )
                )

        definition = z3.BoolVal(True, ctx=self.problem.context)

        for condition, if_true in reversed(entries):
            definition = z3.If(condition, if_true, definition)
        z3.RecAddDefinition(interpret_inst, t, definition)

        return interpret_inst

    def eval(
        self, qf_formula: z3.ExprRef, assignment: Iterable[z3.ExprRef]
    ) -> z3.ExprRef:
        if z3.is_var(qf_formula):
            return z3.substitute_vars(
                qf_formula.translate(self.problem.context), *assignment
            )
        elif z3.is_const(qf_formula):
            return self.constants[qf_formula]
        elif z3.is_and(qf_formula):
            return z3.And(
                *(
                    cast_bool(self.eval(child, assignment))
                    for child in qf_formula.children()
                )
            )
        elif z3.is_or(qf_formula):
            return z3.Or(
                *(
                    cast_bool(self.eval(child, assignment))
                    for child in qf_formula.children()
                )
            )
        elif z3.is_not(qf_formula):
            child = cast_bool(self.eval(qf_formula.children()[0], assignment))
            return z3.Not(child)
        elif z3.is_implies(qf_formula):
            antecedent, consequent = qf_formula.children()
            return z3.Implies(
                cast_bool(self.eval(antecedent, assignment)),
                cast_bool(self.eval(consequent, assignment)),
            )
        elif z3.is_eq(qf_formula):
            left, right = qf_formula.children()
            return self.eval(left, assignment) == self.eval(right, assignment)
        elif z3.is_distinct(qf_formula):
            return z3.Distinct(
                *(
                    cast_bool(self.eval(child, assignment))
                    for child in qf_formula.children()
                )
            )
        else:
            assert z3.is_app(qf_formula)
            assert qf_formula.decl() in self.applications
            return self.applications[qf_formula.decl()](
                *(self.eval(child, assignment) for child in qf_formula.children())
            )

    def add_instantiations(
        self, solver: z3.Solver, instantiations: Iterable[z3.ExprRef]
    ) -> None:
        solver.add(
            z3.And(
                *(
                    cast_bool(self.interpret_instantiation(inst))
                    for inst in instantiations
                )
            )
        )
