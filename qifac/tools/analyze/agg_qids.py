from typing import Dict, Set
from argparse import ArgumentParser, Namespace
import statistics
import sys
from pathlib import Path


def run(args: Namespace) -> None:
    results: Dict[str, Dict[str, Set[int]]] = {}
    for filename in Path(args.dir).glob("*-qids.txt"):
        with open(filename, "r") as file:
            qid = None
            sub_qid = None
            while line := file.readline():
                if "@@@" in line:
                    break
                if qid is None:
                    qid = line.strip()
                    if "!" in qid:
                        qid, sub_qid = qid.split("!")
                    continue
                if "###" in line:
                    qid = None
                    sub_qid = None
                    continue
                amount = int(line)
                results.setdefault(qid, {})
                results[qid].setdefault("_", set())
                results[qid].setdefault(sub_qid, set())
                results[qid]["_"].add(amount)
                if sub_qid is not None:
                    results[qid][sub_qid].add(amount)

    avg_per_file = {qid: statistics.mean(data["_"]) for qid, data in results.items()}
    total = {qid: sum(data["_"]) for qid, data in results.items()}

    per_total: Dict[int, int] = {}
    for qid, total_amount in total.items():
        per_total.setdefault(total_amount, 0)
        per_total[total_amount] += 1

    total_sum = 0
    count = 0
    for amount in sorted(per_total.keys()):
        qids = per_total[amount]
        count += qids
        total_sum += qids * amount
        print(f"{qids} qids with {amount} total instantiations")

    print(f"Average is {total_sum / count}")


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser.add_argument("dir", help="Directory of analytics file")
    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
