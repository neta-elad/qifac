import argparse

from . import tools


def parent() -> None:
    parser = argparse.ArgumentParser(prog="qifac")
    sub_parsers = parser.add_subparsers()

    unsat_core = sub_parsers.add_parser("unsat-core")
    tools.unsat_core.build_parser(unsat_core)
    unsat_core.set_defaults(fun=tools.unsat_core.find_unsat_core)

    booleanize_quantifiers = sub_parsers.add_parser("booleanize-quantifiers")
    tools.booleanize_quantifiers.build_parser(booleanize_quantifiers)
    booleanize_quantifiers.set_defaults(
        fun=tools.booleanize_quantifiers.booleanize_quantifiers
    )

    add_proof = sub_parsers.add_parser("add-proof")
    tools.add_proof.build_parser(add_proof)
    add_proof.set_defaults(fun=tools.add_proof.add_proof)

    find_proof = sub_parsers.add_parser("find-proof")
    tools.find_proof.build_parser(find_proof)
    find_proof.set_defaults(fun=tools.find_proof.find_proof)

    args = parser.parse_args()
    args.fun(args)


if __name__ == "__main__":
    parent()
