from typing import Dict, Set
from argparse import ArgumentParser, Namespace
import statistics

from ...instantiation_set import InstantiationSet, Instantiation, Term


def run(args: Namespace) -> None:
    instantiations: InstantiationSet = args.instantiations
    qids = {qid: len(insts) for qid, insts in instantiations.by_qid().items()}

    for qid, amount in qids.items():
        args.output.write(f"{qid}\n")
        args.output.write(f"{amount}\n")
        args.output.write("###\n")

    args.output.write("@@@\n")

    amounts = list(qids.values())

    args.output.write(f"Max: {max(amounts)}\n")
    args.output.write(f"Mean: {statistics.mean(amounts)}\n")
    args.output.write(f"Variance: {statistics.variance(amounts)}\n")
    args.output.write(f"Median: {statistics.median(amounts)}\n")

    results: Dict[int, Set[str]] = {}

    for qid, amount in qids.items():
        results.setdefault(amount, set())
        results[amount].add(qid)

    for amount in sorted(results.keys()):
        args.output.write(
            f"{len(results[amount])} qids with {amount} instantiation(s)\n"
        )


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    return parser
