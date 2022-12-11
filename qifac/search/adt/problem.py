from dataclasses import dataclass, field
from functools import cached_property
from itertools import chain
from typing import Iterable, List, Mapping, Set, Tuple

import z3


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

    @cached_property
    def quantifiers(self) -> Mapping[int, z3.QuantifierRef]:
        return {q.get_id(): q for q in self.forall_assertions}

    @cached_property
    def instantiation_adt(self) -> z3.DatatypeRef:
        Instantiation = z3.Datatype("Instantiation", ctx=self.context)
        for qid, quantifier in self.quantifiers.items():
            Instantiation.declare(
                f"Inst_{qid}",
                *(
                    (f"Inst_{qid}_{i}", self.ground_term_adt)
                    for i in range(quantifier.num_vars())
                ),
            )

        return Instantiation.create()

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

    def match_instantiation(self, instantiation: z3.ExprRef, qid: int) -> bool:
        matcher = getattr(self.instantiation_adt, f"is_Inst_{qid}")
        simplified = z3.simplify(matcher(instantiation))
        if z3.is_true(simplified):
            return True
        elif z3.is_false(simplified):
            return False
        else:
            raise RuntimeError(f"Unmatchable instantiation {instantiation}")

    def extract_instantiation(
        self, instantiation: z3.ExprRef, qid: int, i: int
    ) -> z3.ExprRef:
        extractor = getattr(self.instantiation_adt, f"Inst_{qid}_{i}")
        return self.adt_to_term(z3.simplify(extractor(instantiation)))

    def apply_instantiation(self, instantiation: z3.ExprRef, qid: int) -> z3.BoolRef:
        quantifier = self.quantifiers[qid]
        return z3.substitute_vars(
            quantifier.body(),
            *(
                self.extract_instantiation(instantiation, qid, i)
                for i in range(quantifier.num_vars())
            ),
        )

    def adt_to_instantiation(self, instantiation: z3.ExprRef) -> z3.BoolRef:
        for qid in self.quantifiers:
            if self.match_instantiation(instantiation, qid):
                return self.apply_instantiation(instantiation, qid)

        raise RuntimeError(f"Unmatched term {instantiation}")
