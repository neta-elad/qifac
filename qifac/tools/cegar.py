import io
import re
import shutil
import tempfile
from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Mapping, Set

import z3
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand, SmtLibScript

from .helpers import normalize, stdio_args


@dataclass
class ScriptHeader:
    script: SmtLibScript
    shared: List[SmtLibCommand]
    funs: Mapping[str, SmtLibCommand]

    @classmethod
    def from_script(cls, script: SmtLibScript) -> "ScriptHeader":
        shared = (
            list(script.filter_by_command_name("set-info"))
            + list(script.filter_by_command_name("set-option"))
            + list(script.filter_by_command_name("declare-sort"))
        )

        funs = {
            normalize(str(fun.args[0])): fun
            for fun in script.filter_by_command_name("declare-fun")
        }

        return cls(script, shared, funs)

    def produce(self, exclude_funs: Set[str]) -> str:
        funs = [fun for name, fun in self.funs.items() if name not in exclude_funs]
        self.script.commands = self.shared + funs

        buffer = io.StringIO()
        self.script.serialize(buffer, daggify=False)

        return buffer.getvalue()

    def model_as_formula(self, model: z3.ModelRef) -> str:
        header = self.produce({normalize(str(decl)) for decl in model.decls()})
        lines = []

        universe: Dict[str, List[str]] = {}

        reading_universe = None
        in_cardinality = False

        universe_line = r";; universe for (.*?):"
        define_line = r"\(define-fun (.*?) "

        defined = set()
        skip_to_define = False

        for line in model.sexpr().splitlines():
            if reading_universe is not None:
                elements = line.replace(";;", "").strip().split(" ")
                universe[reading_universe] = elements
                reading_universe = None
                continue

            match = re.match(universe_line, line)
            if match:
                reading_universe = match.group(1)
                continue

            if in_cardinality:
                if ";;" in line:
                    in_cardinality = False

                continue

            if ";; cardinality constraint:" in line:
                in_cardinality = True

            if line.startswith(";"):
                continue

            match = re.match(define_line, line)

            if match:
                fun = match.group(1)
                if fun in defined:
                    skip_to_define = True
                else:
                    defined.add(fun)
                    skip_to_define = False

            if not skip_to_define:
                lines.append(line)

            # if line not in lines: # ???

        for sort, elements in universe.items():
            equalities = " ".join(f"(= x {element})" for element in elements)
            lines.append(f"(assert (forall ((x {sort})) (or {equalities})))")

        return header + "\n".join(lines)

    def model_as_solver(self, model: z3.ModelRef) -> z3.Solver:
        solver = z3.Solver()
        solver.set(":timeout", 10)
        sexpr = self.model_as_formula(model)
        try:
            solver.from_string(sexpr)
        except Exception as e:
            # print(sexpr)
            print("------ model ------")
            print(model.sexpr())
            print(repr(e))
            exit(-1)
        return solver


def run(args: Namespace) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(args.input, file)

        smt_parser = SmtLibParser()
        script = smt_parser.get_script_fname(str(input_path))

        header = ScriptHeader.from_script(script)

        sexpr = input_path.read_text()

    solver = z3.Solver()
    solver.from_string(sexpr)

    first, *list_asserts = list(solver.assertions())
    asserts = set(list_asserts)
    current_asserts = []

    solver.reset()

    current_asserts.append(first)
    solver.add(first)

    while solver.check() == z3.sat:
        model = solver.model()
        model_solver = header.model_as_solver(model)

        assert model_solver.check() == z3.sat

        added = False

        for formula in asserts:
            model_eval = model.eval(formula, model_completion=True)

            if z3.is_true(model_eval):
                model_solver.add(formula)
            elif z3.is_false(model_eval):
                # print(f"Adding {formula} from eval")
                current_asserts.append(formula)
                asserts.remove(formula)
                solver.add(formula)
                added = True
                break
            else:
                model_solver.push()
                model_solver.add(z3.Not(formula))

                if model_solver.check() == z3.sat:
                    # print(f"Adding {formula} from solver")
                    current_asserts.append(formula)
                    asserts.remove(formula)
                    solver.add(formula)
                    added = True
                    break
                else:
                    model_solver.pop()

        if not added:
            print("Stuck")
            break

    print(current_asserts)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser = stdio_args(parser)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
