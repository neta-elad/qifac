from typing import Set, Dict, Any
from argparse import ArgumentParser, Namespace, FileType
import shutil
import tempfile
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser, Annotations
import z3

from .helpers import stdio_args
from ..pysmt_helpers import AbstractForallWalker


class QidsChecker(AbstractForallWalker):
    annotations: Annotations
    core: str
    encountered_qid: bool
    encountered_qid_in_core: bool

    def __init__(self, annotations: Annotations, core: str):
        super().__init__()
        self.annotations = annotations
        self.core = core
        self.encountered_qid = False
        self.encountered_qid_in_core = False

    def walk_forall(self, formula: Any) -> Any:
        body = formula.args()[0]
        if body in self.annotations and "qid" in self.annotations[body]:
            for qid in self.annotations[body]["qid"]:
                self.encountered_qid = True
                if qid in self.core:
                    self.encountered_qid_in_core = True

        yield body


def run(args: Namespace) -> None:
    smt_parser = SmtLibParser()

    with tempfile.TemporaryDirectory() as tmpdir:
        input_path = Path(tmpdir) / 'input.smt2'
        input_path.write_text(args.input.read())

        core_script = smt_parser.get_script_fname(str(input_path))

        core = '\n'.join([line for line in input_path.read_text().splitlines()
                if "declare-fun" not in line])

    source_script = smt_parser.get_script(args.source)

    core_asserts = list(core_script.filter_by_command_name("assert"))

    asserts = list(source_script.filter_by_command_name("assert"))

    for command in asserts:
        checker = QidsChecker(source_script.annotations, core)
        checker.walk(command.args[0])

        if checker.encountered_qid and not checker.encountered_qid_in_core:
            source_script.commands.remove(command)
        elif not checker.encountered_qid and command not in core_asserts:
            source_script.commands.remove(command)


    source_script.serialize(args.output, daggify=False)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    parser.add_argument(
        "-s",
        "--source",
        required=True,
        type=FileType("r"),
        help="Source of instantiated core",
    )
    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
