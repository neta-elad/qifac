from argparse import ArgumentParser, Namespace
import statistics

from ...instantiation_set import InstantiationSet, Instantiation, Term


def run(args: Namespace) -> None:
    instantiations: InstantiationSet = args.instantiations
    qids = {qid: len(insts) for qid, insts in instantiations.by_qid().items()}
    amounts = list(qids.values())

    print(f"Max: {max(amounts)}")
    print(f"Mean: {statistics.mean(amounts)}")
    print(f"Variance: {statistics.variance(amounts)}")
    print(f"Median: {statistics.median(amounts)}")
    
    results = {}

    for qid, amount in qids.items():
        results.setdefault(amount, set())
        results[amount].add(qid)

    for amount in sorted(results.keys()):
        print(f"{len(results[amount])} qids with {amount} instantiation(s)")

    if args.show is not None:
        for qid in results[args.show]:
            print(qid)


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    parser.add_argument(
        "-s",
        "--show",
        type=int,
        default=None,
        help="Show QIDs (with SHOW instantiations)"
    )

    return parser
