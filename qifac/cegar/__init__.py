import shutil
import tempfile
from dataclasses import dataclass, field
from functools import cached_property
from pathlib import Path
from typing import ClassVar, Dict, List, Set, TextIO, Tuple, TypeVar, cast

import z3
from pysmt.smtlib.parser import SmtLibParser
from tqdm import tqdm

from .hitter import Hitter

AnyExprRef = TypeVar("AnyExprRef", bound=z3.ExprRef)


# for every model: calculate set of unsat asserts
# add all clauses as b -> clause
# check (b1 ... bn)
# minimal hitting set

# when trying a model, try adding as much asserts as possible
# check unknowns everywhere


@dataclass(eq=True, frozen=True)
class ConditionalAssert:
    flag_number: ClassVar[int] = 0

    flag: z3.BoolRef
    formula: z3.BoolRef

    @classmethod
    def auto(cls, formula: z3.BoolRef) -> "ConditionalAssert":
        cls.flag_number += 1
        return cls(z3.Bool(f"bf{cls.flag_number}"), formula)

    @property
    def conditional(self) -> z3.BoolRef:
        return z3.Implies(self.flag, self.formula)

    def as_tuple(self) -> Tuple[z3.BoolRef, "ConditionalAssert"]:
        return (self.flag, self)


@dataclass
class Cegar:
    assertions: Set[z3.BoolRef]
    current: Set[z3.BoolRef] = field(default_factory=lambda: {z3.BoolVal(True)})
    debug: bool = field(default=False)

    @cached_property
    def conditionals(self) -> Dict[z3.BoolRef, ConditionalAssert]:
        return dict(
            ConditionalAssert.auto(formula).as_tuple() for formula in self.assertions
        )

    @cached_property
    def flags(self) -> Set[z3.BoolRef]:
        return set(self.conditionals.keys())

    @cached_property
    def hitter(self) -> Hitter:
        return Hitter(self.flags)

    @cached_property
    def solver(self) -> z3.Solver:
        solver = z3.Solver()
        for conditional in self.conditionals.values():
            solver.add(conditional.conditional)

        return solver

    def run(self) -> Set[z3.BoolRef]:
        while self.solver.check(self.current) != z3.unsat:
            self.run_step()

        print(self.solver.check())
        return {self.conditionals[flag].formula for flag in self.current}

    def run_step(self) -> bool:
        print(f"Checking {len(self.current)} assert(s)")
        model = self.get_model()

        rejects = self.rejects(model)

        print(f"Got {len(rejects)} reject(s)")

        self.hitter.add(rejects)

        self.current = self.hitter.minimum()

        return True

    def get_model(self) -> z3.ModelRef:
        self.solver.set("timeout", 15 * 1_000)

        potentials = self.flags - self.current

        query = set(self.current)

        print("Getting a model...")

        for potential in tqdm(potentials):
            query.add(potential)
            if self.solver.check(query) != z3.sat:
                query.remove(potential)

        self.solver.set("timeout", 0)

        assert self.solver.check(query) != z3.unsat

        print(f"Found model for {len(query)} assert(s)")

        return self.solver.model()

    def rejects(self, model: z3.ModelRef) -> Set[z3.BoolRef]:
        print("Calculating rejects...")

        return {
            conditional.flag
            for conditional in tqdm(self.conditionals.values())
            if self.reject(model, conditional)
        }

    def reject(self, model: z3.ModelRef, conditional: ConditionalAssert) -> bool:
        model_eval = model.eval(conditional.formula, model_completion=False)

        # print(f"Checking {conditional.flag}, got {model_eval}")

        if z3.is_false(model_eval):
            return True
        elif not eval_quantifier(model, model_eval):
            return True

        return False


def cegar(smt_file: TextIO) -> Set[z3.BoolRef]:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        smt_parser = SmtLibParser()
        smt_parser.get_script_fname(str(input_path))

        sexpr = input_path.read_text()

    solver = z3.Solver()
    solver.from_string(sexpr)

    return cegar_from_assertions(set(solver.assertions()))


def cegar_from_assertions(asserts: Set[z3.BoolRef]) -> Set[z3.BoolRef]:
    return Cegar(asserts).run()


def eval_quantifier(model: z3.ModelRef, formula: z3.BoolRef) -> bool:
    unqantified_formula, free_variables = remove_quantifiers(formula)
    interpreted_formula = interpret_functions(
        model, unqantified_formula, free_variables
    )

    universe_constraint = z3.And(
        *[
            z3.Or(
                *[
                    variable == element
                    for element in get_universe(model, variable.decl().range())
                ]
            )
            for variable in free_variables
            if uninterpreted_sort(variable.decl().range())
        ]
    )
    constrained_formula = z3.And(z3.Not(interpreted_formula), universe_constraint)
    model_solver = z3.Solver()
    model_solver.set(timeout=30 * 1_000)
    model_solver.add(constrained_formula)
    # unknown -> ???

    # interpret functions to return the first element from the universe

    return model_solver.check() != z3.sat


def uninterpreted_sort(sort: z3.SortRef) -> bool:
    return sort.kind() == z3.Z3_UNINTERPRETED_SORT


def get_universe(model: z3.ModelRef, sort: z3.SortRef) -> List[z3.Const]:
    return model.get_universe(sort) or [z3.Const(f"{sort}!0", sort)]


def remove_quantifiers(formula: AnyExprRef) -> Tuple[AnyExprRef, Set[z3.Const]]:
    consts = set()

    if z3.is_quantifier(formula):
        fresh_consts = list(
            reversed(
                [
                    z3.FreshConst(formula.var_sort(i), formula.var_name(i))
                    for i in range(formula.num_vars())
                ]
            )
        )
        body = formula.body()
        unquantified_body = z3.substitute_vars(body, *fresh_consts)
        consts.update(fresh_consts)
        recursive_body, recursive_consts = remove_quantifiers(unquantified_body)
        consts.update(recursive_consts)
        return cast(AnyExprRef, recursive_body), consts
    elif z3.is_app(formula):
        if formula.num_args() == 0:
            return formula, consts

        args = []
        for i in range(formula.num_args()):
            arg, arg_consts = remove_quantifiers(formula.arg(i))
            args.append(arg)
            consts.update(arg_consts)

        return clone_formula(formula, args), consts

    raise RuntimeError(f"Unexpected formula type: {formula}")


def interpret_functions(
    model: z3.ModelRef, formula: AnyExprRef, free_variables: Set[z3.Const]
) -> AnyExprRef:
    if not z3.is_app(formula):
        raise RuntimeError(f"Unexpected formula type {formula}")

    universe = get_universe(model, formula.decl().range())

    if formula in free_variables or formula in universe:
        return formula

    if formula.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return cast(AnyExprRef, universe[0])

    args = [
        interpret_functions(model, formula.arg(i), free_variables)
        for i in range(formula.num_args())
    ]

    return clone_formula(formula, args)


def clone_formula(formula: AnyExprRef, args: List[z3.ExprRef]) -> AnyExprRef:
    if z3.is_and(formula):
        return cast(AnyExprRef, z3.And(*cast(List[z3.BoolRef], args)))
    elif z3.is_or(formula):
        return cast(AnyExprRef, z3.Or(*cast(List[z3.BoolRef], args)))
    elif str(formula.decl()) == "+":
        return cast(AnyExprRef, z3.Sum(*cast(List[z3.IntNumRef], args)))
    else:
        return cast(AnyExprRef, formula.decl()(*args))
