from argparse import ArgumentParser, Namespace

from qifac.tools import compact

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

    requantify = sub_parsers.add_parser("requantify")
    tools.requantify.build_parser(requantify)
    requantify.set_defaults(fun=tools.requantify.run)

    uglify = sub_parsers.add_parser("uglify")
    tools.uglify.build_parser(uglify)
    uglify.set_defaults(fun=tools.uglify.run)

    compact = sub_parsers.add_parser("compact")
    tools.compact.build_parser(compact)
    compact.set_defaults(fun=tools.compact.run)

    cegar = sub_parsers.add_parser("cegar")
    tools.cegar.build_parser(cegar)
    cegar.set_defaults(fun=tools.cegar.run)

    compare = sub_parsers.add_parser("compare")
    tools.compare.build_parser(compare)
    compare.set_defaults(fun=tools.compare.run)

    restrict = sub_parsers.add_parser("restrict")
    tools.restrict.build_parser(restrict)
    restrict.set_defaults(fun=tools.restrict.run)

    find_instances = sub_parsers.add_parser("find-instances")
    tools.find_instances.build_parser(find_instances)
    find_instances.set_defaults(fun=tools.find_instances.run)

    compare_instances = sub_parsers.add_parser("compare-instances")
    tools.compare_instances.build_parser(compare_instances)
    compare_instances.set_defaults(fun=tools.compare_instances.run)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
