from argparse import ArgumentParser, Namespace

from . import tools


def run(args: Namespace) -> None:
    args.fun(args)


def build_parser(
    parser: ArgumentParser = ArgumentParser(prog="qifac"),
) -> ArgumentParser:
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

    terms = sub_parsers.add_parser("terms")
    tools.terms.build_parser(terms)
    terms.set_defaults(fun=tools.terms.terms)

    unique_qids = sub_parsers.add_parser("uniq-qids")
    tools.unique_qids.build_parser(unique_qids)
    unique_qids.set_defaults(fun=tools.unique_qids.unique_qids)

    remove_unwanted = sub_parsers.add_parser("remove-unwanted")
    tools.remove_unwanted.build_parser(remove_unwanted)
    remove_unwanted.set_defaults(fun=tools.remove_unwanted.remove_unwanted)

    analyze = sub_parsers.add_parser("analyze")
    tools.analyze.build_parser(analyze)
    analyze.set_defaults(fun=tools.analyze.run)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
