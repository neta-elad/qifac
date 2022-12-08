from dataclasses import dataclass, field
from functools import cached_property
from itertools import chain, product
from typing import Any, Iterable, List, Mapping, Set, Tuple, cast

import z3


def run_adt() -> None:
    print("Running ADT search process")
    problem, terms = consensus()
    print_and_check("Full query", problem.full_query())
    print_and_check("Ground query", problem.ground_query())

    z3_models = problem.generate_models(terms)

    models = [Model(problem, i, model) for i, model in enumerate(z3_models)]

    problem.solve(models)


def print_and_check(title: str, solver: z3.Solver) -> None:
    print(f"{title}:")
    print(solver)
    print(f"=> {solver.check()}")


class Relation(z3.FuncDeclRef):
    def __call__(self, *args: z3.ExprRef) -> z3.BoolRef:
        pass


def cast_relation(relation: z3.FuncDeclRef) -> Relation:
    return cast(Relation, relation)


@dataclass
class Problem:
    sort: z3.SortRef
    constants: Set[z3.Const]
    functions: Set[z3.FuncDeclRef]
    qf_assertions: List[z3.BoolRef]
    forall_assertions: List[z3.QuantifierRef]
    n_terms: int = field(default=5)
    context: z3.Context = field(default_factory=z3.Context)

    def full_query(self) -> z3.Solver:
        solver = z3.Solver()
        solver.add(*chain(self.qf_assertions, self.forall_assertions))
        return solver

    def ground_query(self) -> z3.Solver:
        solver = z3.Solver()
        solver.add(*chain(self.qf_assertions))
        return solver

    def limit(self, solver: z3.Solver, size: int) -> None:
        cs = [z3.Const(f"Size!{i}", self.sort) for i in range(size)]
        y = z3.Const("y", self.sort)
        solver.add(z3.Exists(cs, z3.ForAll([y], z3.Or(*(y == x for x in cs)))))

    def minimize_model(
        self, solver: z3.Solver, size: int = 1
    ) -> Tuple[int, z3.ModelRef]:
        assert solver.check() == z3.sat
        while True:
            solver.push()
            self.limit(solver, size)
            if (res := solver.check()) == z3.sat:
                model = solver.model()
                solver.pop()
                return size, model
            else:
                assert res == z3.unsat
                solver.pop()
                size += 1

    def all_live(
        self, xs: Iterable[z3.Const], live_terms: Iterable[z3.ExprRef]
    ) -> z3.BoolRef:
        return z3.And(*[z3.Or(*[x == t for t in live_terms]) for x in xs])

    def forall_live(
        self, xs: List[z3.Const], live_terms: Iterable[z3.ExprRef], body: z3.BoolRef
    ) -> z3.BoolRef:
        return z3.ForAll(xs, z3.Implies(self.all_live(xs, live_terms), body))

    def generate_models(self, all_live_terms: List[z3.ExprRef]) -> List[z3.ModelRef]:
        models = []
        for i in range(len(all_live_terms) + 1):
            print(f"Checking with {i} live terms:")
            live_terms = all_live_terms[:i]

            s = z3.Solver()
            s.add(*self.qf_assertions)
            for f in self.forall_assertions:
                vs = [
                    z3.Const(f.var_name(i), f.var_sort(i)) for i in range(f.num_vars())
                ]
                s.add(self.forall_live(vs, live_terms, f.body()))
            print(s)
            res = s.check()
            print(res)
            if res == z3.sat:
                size, model = self.minimize_model(s)
                print(size, model)
                models.append(model)
            print()

        return models

    @cached_property
    def ground_term_adt(self) -> z3.DatatypeRef:
        GroundTerm = z3.Datatype("GroundTerm", ctx=self.context)
        for constant in self.constants:
            GroundTerm.declare(f"GT_{constant}")

        for fun in self.functions:
            GroundTerm.declare(
                f"GT_{fun.name()}",
                *((f"GT_{fun.name()}_{i}", GroundTerm) for i in range(fun.arity())),
            )
        return GroundTerm.create()

    def match_term(self, term: z3.ExprRef, fun: z3.FuncDeclRef) -> bool:
        matcher = getattr(self.ground_term_adt, f"is_GT_{fun.name()}")
        simplified = z3.simplify(matcher(term))
        if z3.is_true(simplified):
            return True
        elif z3.is_false(simplified):
            return False
        else:
            raise RuntimeError(f"Unmatchable term {term}")

    def extract_term(self, term: z3.ExprRef, fun: z3.FuncDeclRef, i: int) -> z3.ExprRef:
        extractor = getattr(self.ground_term_adt, f"GT_{fun.name()}_{i}")
        return self.adt_to_term(z3.simplify(extractor(term)))

    def apply_term(self, term: z3.ExprRef, fun: z3.FuncDeclRef) -> z3.ExprRef:
        return fun(*(self.extract_term(term, fun, i) for i in range(fun.arity())))

    def adt_to_term(self, term: z3.ExprRef) -> z3.ExprRef:
        for constant in self.constants:
            if self.match_term(term, constant.decl()):
                return constant

        for fun in self.functions:
            if self.match_term(term, fun):
                return self.apply_term(term, fun)

        raise RuntimeError(f"Unmatched term {term}")

    def solve(self, initial_models: List["Model"]) -> None:
        adt_solver = z3.Solver(ctx=self.context)
        terms_for_instantiation = self.initialize(adt_solver, initial_models)
        models = list(initial_models)
        print(f"\nTrying to do MBQI:\n")
        problem_solver = z3.Solver()
        problem_solver.add(*self.qf_assertions)
        while (result := problem_solver.check()) != z3.unsat:
            assert result == z3.sat
            size, new_ref = self.minimize_model(problem_solver)
            id = len(models)
            print(f"\nFound {id + 1}-th model with {size} elements: \n{new_ref}")
            new_model = Model(self, id, new_ref)
            models.append(new_model)
            new_model.add(adt_solver, terms_for_instantiation)

            result = adt_solver.check()
            print(f"finding new instantiations: {result}")
            ground_instantiations: List[z3.BoolRef] = []
            if result == z3.sat:
                new_adt_model = adt_solver.model()
                for model in models:
                    print(f"model {model.id}:")
                    violated = [
                        new_adt_model[v] is not None and to_bool(new_adt_model[v])
                        for v in model.indicators
                    ]
                    assert any(violated)
                    assert violated.count(True) == 1
                    for i, v in enumerate(violated):
                        if v:
                            print(
                                f"    violates assertion {i}: {self.forall_assertions[i]}"
                            )
                            ws = [new_adt_model[w] for w in model.witnesses[i]]
                            print(f"    witnesses are: {ws}")
                            adts = []
                            for w in ws:
                                eqs = [
                                    to_bool(
                                        z3.simplify(
                                            w
                                            == new_adt_model.eval(
                                                model.interpret(new_adt_model[t])
                                            )
                                        )
                                    )
                                    for t in terms_for_instantiation
                                ]
                                assert any(eqs)
                                j = eqs.index(True)
                                adts.append(new_adt_model[terms_for_instantiation[j]])
                            print(f"    ground term ADTs are: {adts}")
                            ts = [self.adt_to_term(t) for t in adts]
                            print(f"    ground terms are: {ts}")
                            elems = [model.ref.eval(t) for t in ts]
                            print(f"    ground terms evaluate to: {elems}")
                            assert [model.universe.index(e) for e in elems] == [
                                model.elements.index(new_adt_model[w])
                                for w in model.witnesses[i]
                            ]
                            g = z3.substitute_vars(
                                self.forall_assertions[i].body(), *ts
                            )
                            print(f"    ground instance is: {g}")
                            print(f"    it evaluates to: {model.ref.eval(g)}")
                            assert z3.is_false(model.ref.eval(g)), (
                                model.id,
                                ws,
                                adts,
                                ts,
                                elems,
                                g,
                                model.ref.eval(g),
                            )
                            if (
                                len(ground_instantiations) == model.id
                            ):  # append only the first violated in each model
                                ground_instantiations.append(g)
            elif result == z3.unsat:
                print(f"Cannot hit all models with {self.n_terms} ground terms")
                break
            else:
                assert False

            print(f"\nSummary for the {model.id}-th iteration:")
            print(
                f"\nFound the following ADTs:",
                [new_adt_model[t] for t in terms_for_instantiation],
            )
            print(
                f"\nThey correspond to terms:",
                [self.adt_to_term(new_adt_model[t]) for t in terms_for_instantiation],
            )
            print(
                f"\nAll models are hit using the following {len(ground_instantiations)} ground instantiations:"
            )
            for g in ground_instantiations:
                print(f"\n{g}")
                problem_solver.add(g)
        print(f"ADT-based MBQI done! (problem_solver is {problem_solver.check()})")

    def initialize(
        self, solver: z3.Solver, initial_models: List["Model"]
    ) -> List[z3.Const]:
        terms_for_instantiation = [
            z3.Const(f"t_{i}", self.ground_term_adt) for i in range(self.n_terms)
        ]

        for model in initial_models:
            model.add(solver, terms_for_instantiation)

        result = solver.check()
        assert result == z3.sat
        ground_instantiations: List[z3.BoolRef] = []
        adt_model = solver.model()
        for model in initial_models:
            print(f"model {model.id}:")
            violated = [
                adt_model[v] is not None and to_bool(adt_model[v])
                for v in model.indicators
            ]
            assert any(violated)
            assert violated.count(True) == 1
            for i, v in enumerate(violated):
                if v:
                    print(f"    violates assertion {i}: {self.forall_assertions[i]}")
                    ws = [adt_model[w] for w in model.witnesses[i]]
                    print(f"    witnesses are: {ws}")
                    adts = []
                    for w in ws:
                        eqs = [
                            to_bool(
                                z3.simplify(
                                    w == adt_model.eval(model.interpret(adt_model[t]))
                                )
                            )
                            for t in terms_for_instantiation
                        ]
                        assert any(eqs)
                        j = eqs.index(True)
                        adts.append(adt_model[terms_for_instantiation[j]])
                    print(f"    ground term ADTs are: {adts}")
                    ts = [self.adt_to_term(t) for t in adts]
                    print(f"    ground terms are: {ts}")
                    elems = [model.ref.eval(t) for t in ts]
                    print(f"    ground terms evaluate to: {elems}")
                    assert [model.universe.index(e) for e in elems] == [
                        model.elements.index(adt_model[w]) for w in model.witnesses[i]
                    ]
                    g = z3.substitute_vars(self.forall_assertions[i].body(), *ts)
                    print(f"    ground instance is: {g}")
                    print(f"    it evaluates to: {model.ref.eval(g)}")
                    assert z3.is_false(model.ref.eval(g)), (
                        model.id,
                        ws,
                        adts,
                        ts,
                        elems,
                        g,
                        model.ref.eval(g),
                    )
                    if (
                        len(ground_instantiations) == model.id
                    ):  # append only the first violated in each model
                        ground_instantiations.append(g)
        print("\nSummary:")
        print(
            f"\nFound the following ADTs:",
            [adt_model.eval(t) for t in terms_for_instantiation],
        )
        print(
            f"\nThey correspond to terms:",
            [self.adt_to_term(adt_model.eval(t)) for t in terms_for_instantiation],
        )
        print(
            f"\nAll models are hit using the following {len(ground_instantiations)} ground instantiations:"
        )
        for g in ground_instantiations:
            print(f"\n{g}")

        return terms_for_instantiation


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
        for e in reversed(entries):
            definition = z3.If(e[0], e[1], definition)
        z3.RecAddDefinition(interpret, t, definition)

        return interpret

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

    def add(self, solver: z3.Solver, terms: Iterable[z3.ExprRef]) -> None:
        self.add_bodies(solver)
        self.add_indicators(solver)
        self.add_witnesses(solver, terms)


def to_bool(x: Any) -> bool:
    if x is True or x is False:
        return x
    else:
        assert z3.is_true(x) or z3.is_false(x), f"Cannot convert to bool {x}"
        return z3.is_true(x)


def cast_bool(expression: z3.ExprRef) -> z3.BoolRef:
    return cast(z3.BoolRef, expression)


def consensus() -> Tuple[Problem, List[z3.ExprRef]]:
    S = z3.DeclareSort("S")
    node = S
    quorum = S
    value = S

    member = cast_relation(z3.Function("member", node, quorum, z3.BoolSort()))
    intersection = z3.Function("intersection", quorum, quorum, node)
    vote = cast_relation(z3.Function("vote", node, value, z3.BoolSort()))
    decided = cast_relation(z3.Function("decided", value, z3.BoolSort()))
    quorum_of_decided = z3.Function("quorum_of_decided", value, quorum)

    n = z3.Const("n", node)
    # n1 = z3.Const("n1", node)
    # n2 = z3.Const("n2", node)
    v = z3.Const("v", value)
    v1 = z3.Const("v1", value)
    v2 = z3.Const("v2", value)
    z3.Const("q", quorum)
    q1 = z3.Const("q1", quorum)
    q2 = z3.Const("q2", quorum)

    qf_assertions = [
        decided(v1),
        v1 != v2,
    ]

    forall_assertions = [
        z3.ForAll([q1, q2], member(intersection(q1, q2), q1)),
        z3.ForAll([q1, q2], member(intersection(q1, q2), q2)),
        z3.ForAll([n, v1, v2], z3.Implies(z3.And(vote(n, v1), vote(n, v2)), v1 == v2)),
        z3.ForAll(
            [v, n],
            z3.Implies(
                decided(v), z3.Implies(member(n, quorum_of_decided(v)), vote(n, v))
            ),
        ),
        z3.ForAll([n], z3.Implies(member(n, q2), vote(n, v2))),
    ]

    problem = Problem(
        S,
        {v1, v2, q2},
        {intersection, quorum_of_decided},
        qf_assertions,
        forall_assertions,
    )

    return problem, [
        v1,
        v2,
        quorum_of_decided(v1),
        q2,
        intersection(quorum_of_decided(v1), q2),
    ]
