import io
import shutil
import tempfile
from pathlib import Path
from typing import List, TextIO

import z3
from pysmt.smtlib.parser import SmtLibParser

from ..smt.cleaner import clean_errors


def skolemize(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = str(dir_path / "input.smt2")
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        smt_parser = SmtLibParser()
        script = smt_parser.get_script_fname(input_path)
        script.commands = list(script.filter_by_command_name("set-info")) + list(
            script.filter_by_command_name("set-option")
        )

        script.serialize(buffer, daggify=False)

        solver = z3.Tactic("snf").solver()
        solver.set(unsat_core=True)

        solver.from_file(input_path)
        solver.check()

        buffer.write(solver.sexpr())
        buffer.write("\n")

    buffer.write("(check-sat)\n")

    buffer.seek(0)

    return clean_errors(uglify(buffer))


def name(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()

    smt_parser = SmtLibParser()
    script = smt_parser.get_script(smt_file)
    annotations = script.annotations

    for i, cmd in enumerate(script.filter_by_command_name("assert")):
        formula = cmd.args[0]
        if formula not in annotations or "named" not in annotations[formula]:
            annotations.add(formula, "named", f"N{i}")

    buffer.write("(set-option :produce-unsat-cores true)\n")
    buffer.write("(set-option :smt.core.minimize true)\n")
    script.serialize(buffer, daggify=False)
    buffer.write("(get-unsat-core)\n")

    buffer.seek(0)

    return buffer


def filter_names(smt_file: TextIO, names: List[str]) -> TextIO:
    buffer = io.StringIO()
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(smt_file)
    annotations = script.annotations

    asserts = list(script.filter_by_command_name("assert"))

    (get_unsat_core,) = script.filter_by_command_name("get-unsat-core")

    script.commands.remove(get_unsat_core)

    for command in asserts:
        formula = command.args[0]
        if (
            formula not in annotations
            or "named" not in annotations[formula]
            or len(annotations[formula]["named"]) == 0
        ):
            continue

        (name,) = annotations[formula]["named"]

        if name not in names:
            script.commands.remove(command)

    for command in asserts:
        formula = command.args[0]
        annotations.remove_annotation(formula, "named")

    script.serialize(buffer, daggify=False)

    buffer.seek(0)

    return buffer


def uglify(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()
    while line := smt_file.readline():
        stripped = line.rstrip()
        if line.startswith("("):
            buffer.write("\n")
        buffer.write(stripped)

    buffer.seek(0)
    return buffer
