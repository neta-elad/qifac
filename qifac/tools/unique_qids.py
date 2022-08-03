from typing import Dict, Any
from argparse import ArgumentParser, Namespace

from pysmt.smtlib.parser import SmtLibParser, Annotations

from .helpers import stdio_args


def unique_qids(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)

    annotations: Annotations = script.annotations

    used_qids: Dict[str, Any] = {}
    index = 0

    for formula in annotations.all_annotated_formulae("qid"):
        for qid in annotations[formula]["qid"]:
            if qid in used_qids and used_qids[qid] != formula:
                annotations.remove_value(formula, "qid", qid)
                qid = qid + "!" + str(index)
                index += 1
                annotations.add(formula, "qid", qid)

            used_qids[qid] = formula

    script.serialize(args.output, daggify=False)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    unique_qids(build_parser().parse_args())
