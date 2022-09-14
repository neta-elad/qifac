import io
from typing import Any, Dict, Mapping, TextIO

from pysmt.operators import ALL_TYPES, FORALL
from pysmt.shortcuts import Implies, get_free_variables
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.walkers import TreeWalker

from ..instantiation_tree import Forest, Node
from ..pysmt_helpers import AbstractForallWalker, parse_term
from ..tools.helpers import normalize, to_str_dict

all_types_but_forall = list(ALL_TYPES)
all_types_but_forall.remove(FORALL)

Term = Any
Declare = Any
Var = Any


class QuantifierCollector(AbstractForallWalker):
    annotations: Annotations
    quantifiers: Dict[str, Any]

    def __init__(self, annotations: Annotations):
        TreeWalker.__init__(self)
        self.annotations = annotations
        self.quantifiers = {}

    def walk_forall(self, formula: Any) -> Any:
        body = formula.args()[0]
        if body in self.annotations and "qid" in self.annotations[body]:
            for qid in self.annotations[body]["qid"]:
                self.quantifiers[normalize(qid)] = formula

        yield body


def instantiate(smt_file: TextIO, instantiations: Forest) -> TextIO:
    buffer = io.StringIO()
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(smt_file)

    (check_sat,) = script.filter_by_command_name("check-sat")
    script.commands.remove(check_sat)

    collector = QuantifierCollector(script.annotations)
    collector.walk_script(script)

    quantifiers = collector.quantifiers

    formulas = set()

    for node in instantiations.nodes.values():
        formulas.add(instantiate_node(smt_parser, quantifiers, script, node))

    for formula in formulas:
        script.add("assert", [formula])

    script.add_command(check_sat)

    script.serialize(buffer, daggify=False)

    buffer.seek(0)
    return buffer


def instantiate_node(
    parser: SmtLibParser,
    quantifiers: Mapping[str, Term],
    script: SmtLibScript,
    node: Node,
) -> Term:
    if node.has_cycles(set()):
        print(f"{node.qid} has cycles!")
        exit(-1)

    qid = normalize(node.qid)

    quantifier = quantifiers[qid]

    free_variables = to_str_dict(get_free_variables(quantifier.args()[0]))

    all_substitutes = node.all_substitutes()
    parent_substitutes = node.parent_substitutes()

    if node.parent is not None:
        parent_qid = node.forest.nodes[node.parent].qid
        parent_quantifier = quantifiers[normalize(parent_qid)]
        free_variables |= to_str_dict(get_free_variables(parent_quantifier.args()[0]))

    try:
        substitutions = build_substitutions(parser, free_variables, all_substitutes)

        parent_substitutions = build_substitutions(
            parser, free_variables, parent_substitutes
        )
    except KeyError as e:
        print(free_variables)
        raise RuntimeError(f"Could not build substitutions for {node.qid}: {e}")

    instance = quantifier.args()[0].substitute(substitutions)
    parent = quantifier.substitute(parent_substitutions)

    result = Implies(parent, instance)

    substitutes_string = ",".join(
        f"{var}={term}" for var, term in all_substitutes.items()
    )

    name = normalize(f"{node.id}-{node.qid}[{substitutes_string}]")

    script.annotations.add(result, "named", name)

    return result


def build_substitutions(
    parser: SmtLibParser,
    free_variables: Mapping[str, Var],
    substitutes: Mapping[str, str],
) -> Mapping[Var, Term]:
    return {
        free_variables[normalize(var)]: parse_term(parser, term)
        for var, term in substitutes.items()
        if normalize(var) in free_variables
    }


def copy_qid(annotations: Annotations, source: Term, target: Term) -> None:
    source_annotations = annotations[source.args()[0]]
    if source_annotations is not None and "qid" in source_annotations:
        qids = source_annotations["qid"]

        for qid in qids:
            annotations.add(target.args()[0], "qid", qid)
