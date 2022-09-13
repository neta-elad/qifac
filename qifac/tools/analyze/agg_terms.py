from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Dict


def run(args: Namespace) -> None:
    results: Dict[int, int] = {}
    for filename in Path(args.dir).glob("*-depths.txt"):
        with open(filename, "r") as file:
            reading_qid = True
            while line := file.readline():
                if "@@@" in line:
                    break
                if reading_qid:
                    reading_qid = False
                    continue
                if "###" in line:
                    reading_qid = True
                    continue
                depth = int(line)
                results.setdefault(depth, 0)
                results[depth] += 1

    sum = 0
    count = 0
    for depth in sorted(results.keys()):
        amount = results[depth]
        count += amount
        sum += amount * depth
        print(f"{amount} terms of depth {depth}")

    print(f"Average is {sum / count}")


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser.add_argument("dir", help="Directory of analytics file")
    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
