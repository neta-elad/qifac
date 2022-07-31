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

    name = sub_parsers.add_parser("name")
    tools.name.build_parser(name)
    name.set_defaults(fun=tools.name.name)

    filter = sub_parsers.add_parser("filter")
    tools.filter_named.build_parser(filter)
    filter.set_defaults(fun=tools.filter_named.filter_named)

    skolemize = sub_parsers.add_parser("skolemize")
    tools.skolemize.build_parser(skolemize)
    skolemize.set_defaults(fun=tools.skolemize.skolemize)

    prettify = sub_parsers.add_parser("prettify")
    tools.prettify.build_parser(prettify)
    prettify.set_defaults(fun=tools.prettify.prettify)

    instantiate = sub_parsers.add_parser("instantiate")
    tools.instantiate.build_parser(instantiate)
    instantiate.set_defaults(fun=tools.instantiate.instantiate)

    args = parser.parse_args()
    args.fun(args)


if __name__ == "__main__":
    parent()
