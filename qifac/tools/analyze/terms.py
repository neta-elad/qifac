from argparse import ArgumentParser, Namespace
import statistics

from ...instantiation_set import InstantiationSet, Instantiation, Term


def run(args: Namespace) -> None:
    instantiations: InstantiationSet = args.instantiations
    depths = list(_depth(term) for term in instantiations.terms())

    print(f"Max: {max(depths)}")
    print(f"Mean: {statistics.mean(depths)}")
    print(f"Variance: {statistics.variance(depths)}")
    print(f"Median: {statistics.median(depths)}")
    
    results = {}

    for depth in depths:
        results.setdefault(depth, 0)
        results[depth] += 1

    for depth in sorted(results.keys()):
        print(f"{results[depth]} terms of depth {depth}")




def _depth(term: Term) -> int:
    args = term.args()
    if len(args) == 0:
        return 0
    else:
        return 1 + max(_depth(sub_term) for sub_term in args)


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    return parser
