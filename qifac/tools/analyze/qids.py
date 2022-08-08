from argparse import ArgumentParser, Namespace
import statistics

from ...instantiation_set import InstantiationSet, Instantiation, Term


def run(args: Namespace) -> None:
    instantiations: InstantiationSet = args.instantiations
    qids = {qid: len(insts) for qid, insts in instantiations.by_qid().items()}
    amounts = list(qids.values())

    print(max(amounts))
    print(statistics.mean(amounts))
    print(statistics.variance(amounts))
    print(statistics.median(amounts))


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    return parser
