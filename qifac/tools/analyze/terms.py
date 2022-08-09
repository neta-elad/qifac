from argparse import ArgumentParser, Namespace
import statistics

from ...instantiation_set import InstantiationSet, Instantiation, Term


def run(args: Namespace) -> None:
    instantiations: InstantiationSet = args.instantiations
    depths = list(_depth(term) for term in instantiations.terms())

    max_depth = max(depths)

    print(f"Max: {max_depth}")
    print(f"Mean: {statistics.mean(depths)}")
    print(f"Variance: {statistics.variance(depths)}")
    print(f"Median: {statistics.median(depths)}")
    
    results = {}

    for depth in depths:
        results.setdefault(depth, 0)
        results[depth] += 1

    for depth in sorted(results.keys()):
        print(f"{results[depth]} terms of depth {depth}")

    for term in instantiations.terms():
        if _depth(term) == max_depth:
            print(term)




def _depth(term: Term) -> int:
    args = term.args()
    if len(args) == 0:
        return 0
    else:
        return 1 + max(_depth(sub_term) for sub_term in args)


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    return parser
