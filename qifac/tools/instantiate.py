import tempfile
from typing import Set, Dict, Any, TypeVar, Mapping, Optional, TextIO
from argparse import ArgumentParser, Namespace, FileType
from pathlib import Path
import io

from pysmt.smtlib.parser import SmtLibParser, SmtLibScript
from pysmt.smtlib.annotations import Annotations
from pysmt.shortcuts import get_free_variables, Implies

from pysmt.walkers import TreeWalker, handles
from pysmt.operators import ALL_TYPES, FORALL

from .helpers import stdio_args
from ..instantiation_tree import Forest, Node


all_types_but_forall = list(ALL_TYPES)
all_types_but_forall.remove(FORALL)

Term = Any
Declare = Any
Var = Any


class QuantifierCollector(TreeWalker):
    quantifiers: Dict[str, Any]

    def __init__(self, annotations: Annotations):
        TreeWalker.__init__(self)
        self.annotations = annotations
        self.quantifiers = {}

    @handles(all_types_but_forall)
    def walk_error(self, formula: Any, **kwargs: Any) -> Any:
        return self.walk_skip(formula)

    def walk_forall(self, formula: Any) -> Any:
        body = formula.args()[0]
        if body in self.annotations and "qid" in self.annotations[body]:
            for qid in self.annotations[body]["qid"]:
                self.quantifiers[qid] = formula

        yield body


def instantiate(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)

    (check_sat,) = script.filter_by_command_name("check-sat")
    script.commands.remove(check_sat)

    collector = QuantifierCollector(script.annotations)

    for cmd in script.filter_by_command_name("assert"):
        collector.walk(cmd.args[0])

    quantifiers = collector.quantifiers

    forest = Forest.parse(args.instances.readlines())

    formulas = set()

    for node in forest.nodes.values():
        formulas.add(_instantiate(smt_parser, quantifiers, script, node, args.full))

    for formula in formulas:
        script.add("assert", [formula])

    script.add_command(check_sat)

    for formula in script.annotations.all_annotated_formulae("pattern"):
        script.annotations.remove_annotation(formula, "pattern")

    script.serialize(args.output, daggify=False)


def _instantiate(
    parser: SmtLibParser,
    quantifiers: Mapping[str, Term],
    script: SmtLibScript,
    node: Node,
    full: Optional[TextIO],
) -> Term:
    qid = _normalize(node.qid)
    quantifier = quantifiers[qid]

    free_variables = _str_dict(get_free_variables(quantifier.args()[0]))

    all_substitutes = node.all_substitutes()
    parent_substitutes = node.parent_substitutes()

    if node.parent is not None:
        parent_qid = node.forest.nodes[node.parent].qid
        parent_quantifier = quantifiers[_normalize(parent_qid)]
        free_variables |= _str_dict(get_free_variables(parent_quantifier.args()[0]))

    substitutions = _build_substitutions(parser, free_variables, all_substitutes)

    parent_substitutions = _build_substitutions(
        parser, free_variables, parent_substitutes
    )

    instance = quantifier.args()[0].substitute(substitutions)
    parent = quantifier.substitute(parent_substitutions)

    # if quantifier != parent:
    #     copy_qid(script.annotations, quantifier, parent)

    result = Implies(parent, instance)

    substitutes_string = ",".join(
        f"{var}={term}" for var, term in all_substitutes.items()
    )

    name = _normalize(f"{node.qid}[{substitutes_string}]")

    script.annotations.add(result, "named", name)

    if full is not None:
        full.write(name)
        full.write("\n")
        full.write(qid)
        full.write("\n")
        for var, term in all_substitutes.items():
            full.write(var)
            full.write("\n")
            full.write(term)
            full.write("\n")
        full.write("###")
        full.write("\n")

    return result


def _build_substitutions(
    parser: SmtLibParser,
    free_variables: Mapping[str, Var],
    substitutes: Mapping[str, str],
) -> Mapping[Var, Term]:
    return {
        free_variables[_normalize(var)]: _build_term(parser, term)
        for var, term in substitutes.items()
    }


def _copy_qid(annotations: Annotations, source: Term, target: Term) -> None:
    source_annotations = annotations[source.args()[0]]
    if source_annotations is not None and "qid" in source_annotations:
        qids = source_annotations["qid"]

        for qid in qids:
            annotations.add(target.args()[0], "qid", qid)


def _build_term(parser: SmtLibParser, term: str) -> Term:
    buffer = io.StringIO(f"(assert (= {term} {term}))")

    for cmd in parser.get_command_generator(buffer):
        return cmd.args[0].args()[0]


def _normalize(symbol: str) -> str:
    return symbol.replace("|", "").replace("'", "")
    if (symbol.startswith("|") and symbol.endswith("|")) or (
        symbol.startswith("'") and symbol.endswith("'")
    ):
        return symbol[1:-1]
    return symbol


T = TypeVar("T")


def _str_dict(a_set: Set[T]) -> Dict[str, T]:
    return {_normalize(str(value)): value for value in a_set}


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)

    parser.add_argument(
        "-i",
        "--instances",
        required=True,
        type=FileType("r"),
        help="Instantiations file",
    )

    parser.add_argument(
        "-f", "--full", type=FileType("w"), help="write the full instances"
    )

    return parser


if __name__ == "__main__":
    instantiate(build_parser().parse_args())
