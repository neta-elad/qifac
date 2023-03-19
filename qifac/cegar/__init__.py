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

MODEL_EXTENSION_TIMEOUT = 5
MODEL_EVAL_TIMEOUT = 0
DEFAULT_TIMEOUT = 0


# for every model: calculate set of unsat asserts
# add all clauses as b -> clause
# check (b1 ... bn)
# minimal hitting set

# when trying a model, try adding as much asserts as possible
# check unknowns everywhere


# cache remove quantifier ahead
# formula with a function that the model doesn't interpret is automatically rejected
# cache universe constraints per model

# or universe constraints with universal quantifier

# pruning/approximate needed assertions according to last assert


@dataclass(eq=True, frozen=True)
class ConditionalAssert:
    flag_number: ClassVar[int] = 0

    flag: z3.BoolRef
    formula: z3.BoolRef

    @classmethod
    def auto(cls, formula: z3.BoolRef) -> "ConditionalAssert":
        cls.flag_number += 1
        return cls(z3.Bool(f"bf{cls.flag_number}"), formula)

    @cached_property
    def conditional(self) -> z3.BoolRef:
        return z3.Implies(self.flag, self.formula)

    @cached_property
    def quantifier_free_with_variables(self) -> Tuple[z3.BoolRef, Set[z3.Const]]:
        return remove_quantifiers(self.formula)

    @cached_property
    def quantifier_free(self) -> z3.BoolRef:
        return self.quantifier_free_with_variables[0]

    @cached_property
    def variables(self) -> Set[z3.Const]:
        return self.quantifier_free_with_variables[1]

    @cached_property
    def uninterpreted_symbols(self) -> Set[z3.FuncDeclRef]:
        return uninterpreted_symbols(self.quantifier_free)

    def as_tuple(self) -> Tuple[z3.BoolRef, "ConditionalAssert"]:
        return (self.flag, self)


@dataclass
class Cegar:
    assertions: Set[z3.BoolRef]
    preamble: Set[z3.BoolRef] = field(default_factory=set)
    current: Set[z3.BoolRef] = field(default_factory=lambda: {z3.BoolVal(True)})
    debug: bool = field(default=False)

    @classmethod
    def from_solver(cls, solver: z3.Solver) -> "Cegar":
        assertions = list(solver.assertions())
        last_assertion = assertions.pop()
        return cls(set(assertions), {last_assertion})

    @cached_property
    def quantifier_free(self) -> Set[z3.BoolRef]:
        return {
            assertion for assertion in self.assertions if is_quantifier_free(assertion)
        }

    @cached_property
    def quantified(self) -> Set[z3.BoolRef]:
        return {
            assertion
            for assertion in self.assertions
            if not is_quantifier_free(assertion)
        }

    @cached_property
    def conditionals(self) -> Dict[z3.BoolRef, ConditionalAssert]:
        return dict(
            ConditionalAssert.auto(formula).as_tuple() for formula in self.quantified
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

        solver.set("mbqi", False)

        for formula in self.quantifier_free:
            solver.add(formula)

        for formula in self.quantified:
            solver.add(formula)

        # for formula in self.preamble:
        #     solver.add(formula)

        # for conditional in self.conditionals.values():
        #     solver.add(conditional.conditional)

        return solver

    def run(self) -> Set[z3.BoolRef]:
        while self.solver.check(self.current) != z3.unsat:
            model = self.solver.model()
            rejects = self.rejects(model)
            print(f"Got {len(rejects)} rejects")
            for reject in rejects:
                print(f"> {reject.formula.sexpr()}")
            exit(0)

        print(self.solver.check(self.quantified))
        print(self.solver.model().decls())
        exit(0)

        while self.solver.check(self.current) != z3.unsat:
            self.run_step()

        # print(self.solver.check())
        return self.current | self.quantifier_free

    def run_step(self) -> bool:
        print(f"Checking {len(self.current)} assert(s)")

        for assertion in self.current:
            print(f"> {assertion.sexpr()}")

        model = self.get_model()

        rejects = self.rejects(model)

        print(f"Got {len(rejects)} reject(s)")

        self.hitter.add({reject.flag for reject in rejects})

        self.current = {self.conditional(flag) for flag in self.hitter.minimum()}

        return True

    def get_model(self) -> z3.ModelRef:
        self.solver.set(timeout=MODEL_EXTENSION_TIMEOUT)

        potentials = self.quantified - self.current

        query = set(self.current)

        print("Getting a model...")

        for potential in tqdm(potentials):
            query.add(potential)
            if self.solver.check(query) != z3.sat:
                query.remove(potential)

        self.solver.set(timeout=DEFAULT_TIMEOUT)

        assert self.solver.check(query) != z3.unsat

        print(f"Found model for {len(query)} assert(s)")

        return self.solver.model()

    def rejects(self, model: z3.ModelRef) -> Set[ConditionalAssert]:
        print("Calculating rejects...")

        return {
            conditional
            for conditional in tqdm(self.conditionals.values())
            if self.reject(model, conditional)
        }

    def reject(self, model: z3.ModelRef, conditional: ConditionalAssert) -> bool:
        model_eval = model.eval(conditional.quantifier_free, model_completion=False)

        # print(f"Checking {conditional.flag}, got {model_eval}")

        if z3.is_false(model_eval):
            return True
        elif not eval_quantifier(model, model_eval, conditional):
            if conditional.formula in self.current:
                print("---")
                print({f.sexpr() for f in self.current})
                print("---")
                print(conditional.formula.sexpr())
                print("---")
                print(model_eval.sexpr())
                print("---")
                print(model.decls())
                print("---")
                print(conditional.uninterpreted_symbols)
                print("---")
                print(conditional.uninterpreted_symbols - set(model.decls()))
                exit(0)
            return True

        return False

    def conditional(self, flag: z3.BoolRef) -> z3.BoolRef:
        return self.conditionals[flag].formula


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

    return Cegar.from_solver(solver).run()


def cegar_from_assertions(asserts: Set[z3.BoolRef]) -> Set[z3.BoolRef]:
    return Cegar(asserts).run()


def eval_quantifier(
    model: z3.ModelRef, formula: z3.BoolRef, source: ConditionalAssert
) -> bool:
    if not source.uninterpreted_symbols <= set(model.decls()):
        return True
    # else:
    #     return True
    # unqantified_formula, free_variables = remove_quantifiers(formula)
    # return True
    # interpreted_formula = interpret_functions(
    #     model, unqantified_formula, free_variables
    # )

    # model_solver = z3.SolverFor("ALL")
    # model_solver.set('mbqi', True)
    model_solver = z3.Solver()
    model_solver.set("mbqi", False)
    # model_solver.set(timeout=MODEL_EVAL_TIMEOUT)
    model_solver.add(z3.Not(formula))

    # for i in range(model.num_sorts()):
    #     sort = model.get_sort(i)
    #     x = z3.FreshConst(sort)
    #     model_solver.add(z3.ForAll(x, z3.Or(
    #             *[
    #                 x == z3.Const(f"my-{element}", sort)
    #                 for element in get_universe(model, sort)
    #             ]
    #         )))

    for variable in source.variables:
        if not uninterpreted_sort(variable.decl().range()):
            continue

        model_solver.add(
            z3.Or(
                *[
                    variable == element
                    for element in get_universe(model, variable.decl().range())
                ]
            )
        )

    # unknown -> ???

    result = model_solver.check()

    if result == z3.unknown:
        print(source.uninterpreted_symbols)
        print(model.decls())
        print(model_solver.sexpr())
        print(model_solver.reason_unknown())
        exit(-1)

    return result == z3.unsat

    # return True


def uninterpreted_sort(sort: z3.SortRef) -> bool:
    return sort.kind() == z3.Z3_UNINTERPRETED_SORT


def get_universe(model: z3.ModelRef, sort: z3.SortRef) -> List[z3.Const]:
    return model.get_universe(sort) or [z3.Const(f"{sort}!0", sort)]


def is_quantifier_free(formula: z3.ExprRef) -> bool:
    if z3.is_quantifier(formula):
        return False
    elif z3.is_app(formula):
        for i in range(formula.num_args()):
            if not is_quantifier_free(formula.arg(i)):
                return False

        return True

    raise RuntimeError(f"Unexpected formula type: {formula}")


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


def uninterpreted_symbols(formula: z3.ExprRef) -> Set[z3.FuncDeclRef]:
    symbols: Set[z3.FuncDeclRef] = set()
    accumulate_uninterpreted_symbols(formula, symbols)
    return symbols


def accumulate_uninterpreted_symbols(
    formula: z3.ExprRef, symbols: Set[z3.FuncDeclRef]
) -> None:
    if not z3.is_app(formula):
        raise RuntimeError(f"Unexpected formula type {formula}")

    decl = formula.decl()

    if decl.kind() == z3.Z3_OP_UNINTERPRETED:
        symbols.add(decl)

    for i in range(formula.num_args()):
        accumulate_uninterpreted_symbols(formula.arg(i), symbols)
