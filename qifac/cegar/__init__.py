import shutil
import tempfile
from pathlib import Path
from typing import List, Set, TextIO, Tuple, TypeVar, cast

import z3
from pysmt.smtlib.parser import SmtLibParser

AnyExprRef = TypeVar("AnyExprRef", bound=z3.ExprRef)


def cegar(smt_file: TextIO) -> List[z3.BoolRef]:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        smt_parser = SmtLibParser()
        smt_parser.get_script_fname(str(input_path))

        # header = ScriptHeader.from_script(script)

        sexpr = input_path.read_text()

    solver = z3.Solver()
    solver.from_string(sexpr)

    return cegar_from_solver(solver)


def cegar_from_solver(solver: z3.Solver) -> List[z3.BoolRef]:
    first, *list_asserts = list(solver.assertions())
    asserts = list(list_asserts)  # or set?
    current_asserts = []

    solver.reset()

    current_asserts.append(first)
    solver.add(first)

    while solver.check() == z3.sat:
        model = solver.model()

        added = False

        for formula in asserts:
            model_eval = model.eval(formula, model_completion=False)

            if z3.is_false(model_eval):
                current_asserts.append(formula)
                asserts.remove(formula)
                solver.add(formula)
                added = True
                break
            else:
                if not eval_quantifier(model, model_eval):
                    current_asserts.append(formula)
                    asserts.remove(formula)
                    solver.add(formula)
                    added = True
                    break

        if not added:
            raise RuntimeError("CEGAR cannot make progress")

    return current_asserts


def eval_quantifier(model: z3.ModelRef, formula: z3.BoolRef) -> bool:
    unqantified_formula, free_variables = remove_quantifiers(formula)

    # for variable in free_variables:
    #     if (
    #         uninterpreted_sort(variable.decl().range())
    #         and model.get_universe(variable.decl().range()) is None
    #     ):
    #         raise RuntimeError(
    #             f"""
    #         Missing sort {variable.decl().range()} for {variable}
    #         while evaluating
    #             {unqantified_formula.sexpr()}
    #         under {model}
    #         """
    #         )

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
    constrained_formula = z3.And(z3.Not(unqantified_formula), universe_constraint)
    model_solver = z3.Solver()
    return model_solver.check(constrained_formula) != z3.sat


def uninterpreted_sort(sort: z3.SortRef) -> bool:
    return sort not in {z3.BoolSort(), z3.IntSort(), z3.RoundTowardZero().sort()}


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

        result: z3.ExprRef

        if z3.is_and(formula):
            result = z3.And(*cast(List[z3.BoolRef], args))
        elif z3.is_or(formula):
            result = z3.Or(*cast(List[z3.BoolRef], args))
        else:
            result = formula.decl()(*args)

        return cast(AnyExprRef, result), consts

    raise RuntimeError(f"Unexpected formula type: {formula}")
