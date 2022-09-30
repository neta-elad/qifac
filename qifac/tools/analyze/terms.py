import statistics
from argparse import ArgumentParser, Namespace
from typing import Dict

from qifac.parsing.instantiation_set import InstantiationSet, Term


def run(args: Namespace) -> None:
    instantiations: InstantiationSet = args.instantiations

    for instantiation in instantiations.instantiations:
        qid = instantiation.qid
        args.output.write(f"{qid}\n")
        for term in instantiation.terms():
            args.output.write(f"{_depth(term)}\n")
        args.output.write("###\n")

    args.output.write("@@@\n")
    depths = list(_depth(term) for term in instantiations.terms())

    max_depth = max(depths)

    args.output.write(f"Max: {max_depth}\n")
    args.output.write(f"Mean: {statistics.mean(depths)}\n")
    args.output.write(f"Variance: {statistics.variance(depths)}\n")
    args.output.write(f"Median: {statistics.median(depths)}\n")

    results: Dict[int, int] = {}

    for depth in depths:
        results.setdefault(depth, 0)
        results[depth] += 1

    for depth in sorted(results.keys()):
        args.output.write(f"{results[depth]} terms of depth {depth}\n")

    for term in instantiations.terms():
        if _depth(term) == max_depth:
            args.output.write(f"{term}\n")


def _depth(term: Term) -> int:
    args = term.args()
    if len(args) == 0:
        return 0
    else:
        return 1 + max(_depth(sub_term) for sub_term in args)


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    return parser
