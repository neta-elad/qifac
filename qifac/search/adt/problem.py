from dataclasses import dataclass, field
from functools import cached_property
from itertools import chain
from typing import Dict, Iterable, List, Set, Tuple, cast

import z3

from .utils import Relation


def identify_variables(formula: z3.ExprRef) -> List[z3.SortRef]:
    variables = []
    if z3.is_quantifier(formula):
        variables = [formula.var_sort(i) for i in range(formula.num_vars())]

    for child in formula.children():
        variables += identify_variables(child)

    return variables


def instantiate_all(formula: z3.ExprRef, terms: List[z3.ExprRef]) -> z3.ExprRef:
    if z3.is_quantifier(formula):
        num_vars = formula.num_vars()
        first_terms = reversed(terms[:num_vars])
        rest_terms = terms[num_vars:]
        instantiation = z3.substitute_vars(formula.body(), *first_terms)
        return instantiate_all(instantiation, rest_terms)
    elif z3.is_not(formula):
        sub_formula = cast(z3.BoolRef, instantiate_all(formula.children()[0], terms))
        return z3.Not(sub_formula)
    elif z3.is_implies(formula):
        antecedent, consequent = formula.children()
        instantiated_antecedent = cast(z3.BoolRef, instantiate_all(antecedent, terms))
        instantiated_consequent = cast(z3.BoolRef, instantiate_all(consequent, terms))
        return z3.Implies(instantiated_antecedent, instantiated_consequent)
    elif z3.is_or(formula):
        return z3.Or(
            *[
                cast(z3.BoolRef, instantiate_all(child, terms))
                for child in formula.children()
            ]
        )
    elif z3.is_and(formula):
        return z3.And(
            *[
                cast(z3.BoolRef, instantiate_all(child, terms))
                for child in formula.children()
            ]
        )
    else:
        return formula


@dataclass
class QuantifiedAssertion:
    assertion: z3.BoolRef

    @cached_property
    def variables(self) -> List[z3.SortRef]:
        return identify_variables(self.assertion)

    @cached_property
    def num_vars(self) -> int:
        return len(self.variables)

    def instantiate(self, *terms: z3.ExprRef) -> z3.BoolRef:
        return cast(z3.BoolRef, instantiate_all(self.assertion, list(terms)))


@dataclass
class Problem:
    sort: z3.SortRef
    constants: Set[z3.Const]
    functions: Set[z3.FuncDeclRef]
    relations: Set[Relation]
    qf_assertions: List[z3.BoolRef]
    forall_assertions: List[z3.QuantifierRef]
    context: z3.Context = field(default_factory=z3.Context)

    @cached_property
    def quantified_assertions(self) -> List[QuantifiedAssertion]:
        return [QuantifiedAssertion(assertion) for assertion in self.forall_assertions]

    @cached_property
    def sorts(self) -> Set[z3.SortRef]:
        return {self.sort}

    @cached_property
    def sort_constants(self) -> Dict[z3.SortRef, Set[z3.Const]]:
        result: Dict[z3.SortRef, Set[z3.Const]] = {}
        for const in self.constants:
            sort = const.decl().range()
            result.setdefault(sort, set())
            result[sort].add(const)

        return result

    @cached_property
    def sort_functions(self) -> Dict[z3.SortRef, Set[z3.FuncDeclRef]]:
        result: Dict[z3.SortRef, Set[z3.FuncDeclRef]] = {}
        for fun in self.functions:
            sort = fun.range()
            result.setdefault(sort, set())
            result[sort].add(fun)

        return result

    def full_query(self) -> z3.Solver:
        solver = z3.Solver()
        solver.add(*chain(self.qf_assertions, self.forall_assertions))
        return solver

    def ground_query(self) -> z3.Solver:
        solver = z3.Solver()
        solver.add(*chain(self.qf_assertions))
        return solver

    def limit(self, solver: z3.Solver, size: int) -> None:
        for sort in self.sorts:
            cs = [z3.Const(f"{sort}!Size!{i}", sort) for i in range(size)]
            y = z3.Const(f"{sort}!y", sort)
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
    def ground_term_adts(self) -> Dict[z3.SortRef, z3.DatatypeSortRef]:
        pre_sorts = {
            sort: z3.Datatype(f"{sort}_GroundTerm", ctx=self.context)
            for sort in self.sorts
        }

        for sort, constants in self.sort_constants.items():
            for const in constants:
                pre_sorts[sort].declare(f"{sort}_GT_{const}")

        for sort, functions in self.sort_functions.items():
            for fun in functions:
                pre_sorts[sort].declare(
                    f"{sort}_GT_{fun.name()}",
                    *(
                        (f"{sort}_GT_{fun.name()}_{i}", pre_sorts[fun.domain(i)])
                        for i in range(fun.arity())
                    ),
                )

        return dict(zip(self.sorts, z3.CreateDatatypes(*pre_sorts.values())))

    @cached_property
    def ground_term_adts_to_sort(self) -> Dict[z3.SortRef, z3.SortRef]:
        return {datatype: sort for sort, datatype in self.ground_term_adts.items()}

    @cached_property
    def ground_term_adt(self) -> z3.DatatypeSortRef:
        return self.ground_term_adts[self.sort]

    @cached_property
    def instantiation_adt(self) -> z3.DatatypeSortRef:
        Instantiation = z3.Datatype("Instantiation", ctx=self.context)
        for qid, quantifier in enumerate(self.forall_assertions):
            Instantiation.declare(
                f"Inst_{qid}",
                *(
                    (f"Inst_{qid}_{i}", self.ground_term_adt)
                    for i in range(quantifier.num_vars())
                ),
            )

        return Instantiation.create()

    def match_term(self, term: z3.ExprRef, fun: z3.FuncDeclRef) -> bool:
        sort = fun.range()
        matcher = getattr(self.ground_term_adts[sort], f"is_{sort}_GT_{fun.name()}")
        simplified = z3.simplify(matcher(term))
        if z3.is_true(simplified):
            return True
        elif z3.is_false(simplified):
            return False
        else:
            raise RuntimeError(f"Unmatchable term {term}")

    def extract_term(self, term: z3.ExprRef, fun: z3.FuncDeclRef, i: int) -> z3.ExprRef:
        sort = fun.range()
        extractor = getattr(self.ground_term_adts[sort], f"{sort}_GT_{fun.name()}_{i}")
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

    def apply_instantiation(
        self, instantiation: z3.ExprRef, qid: int, quantifier: z3.QuantifierRef
    ) -> z3.BoolRef:
        return z3.substitute_vars(
            quantifier.body(),
            *self.instantiation_args(instantiation, qid, quantifier),
        )

    def instantiation_args(
        self, instantiation: z3.ExprRef, qid: int, quantifier: z3.QuantifierRef
    ) -> List[z3.ExprRef]:
        return [
            self.extract_instantiation(instantiation, qid, i)
            for i in range(quantifier.num_vars())
        ]

    def adt_to_instantiation(self, instantiation: z3.ExprRef) -> z3.BoolRef:
        for qid, quantifier in enumerate(self.forall_assertions):
            if self.match_instantiation(instantiation, qid):
                return self.apply_instantiation(instantiation, qid, quantifier)

        raise RuntimeError(f"Unmatched instantiation {instantiation}")
