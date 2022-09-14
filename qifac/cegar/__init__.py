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
                if eval_quantifier(model, model_eval) == z3.sat:
                    current_asserts.append(formula)
                    asserts.remove(formula)
                    solver.add(formula)
                    added = True
                    break

        if not added:
            raise RuntimeError("CEGAR cannot make progress")

    return current_asserts


def eval_quantifier(model, formula):
    unqantified_formula, free_variables = remove_quantifiers(formula)
    universe_constraint = z3.And(
        *[
            z3.Or(
                *[
                    variable == element
                    for element in model.get_universe(
                        variable.decl().range()
                    )
                ]
            )
            for variable in free_variables
        ]
    )
    constrained_formula = z3.And(
        z3.Not(unqantified_formula), universe_constraint
    )
    model_solver = z3.Solver()
    check = model_solver.check(constrained_formula)
    return check


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

        return cast(AnyExprRef, formula.decl()(*args)), consts

    raise RuntimeError(f"Unexpected formula type: {formula}")
