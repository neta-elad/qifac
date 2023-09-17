import itertools
from typing import Mapping, Tuple, Iterable

import pytest
import z3
from dd.autoref import Function as BDDFunction

from qifac.search.bdd.fixpoint import Fixpoint
from qifac.search.bdd.system import System
from qifac.search.bdd.vector import Vector


def indices(
    vectors: Mapping[z3.ExprRef, Vector[z3.Const]]
) -> Mapping[z3.ExprRef, Tuple[int, ...]]:
    return {key: vector.indices for key, vector in vectors.items()}


def test_reconstruction(system: System) -> None:
    """
    Tries to evaluate and reconstruct all constants and
    functions on constants in the system, and checks that
    the evaluation on the reconstructed value is consistent.
    """
    fixpoint = Fixpoint(system)
    for c in system.problem.constants:
        assert c == fixpoint.reconstruct(system.eval(c))
    for f in system.problem.functions:
        for consts in itertools.product(system.problem.constants, repeat=f.arity()):
            original = f(*consts)
            if system.eval(original) in fixpoint.reachable_vectors.values():
                reconstructed = fixpoint.reconstruct(system.eval(original))
                print(f"{original=}, {reconstructed=}")
                assert system.eval(original) == system.eval(reconstructed)


def get_applications(f: z3.FuncDeclRef, inputs: Iterable):
    for input in itertools.product(inputs, repeat=f.arity()):
        yield f(*input)


def test_fixpoint_stability(system: System) -> None:
    """
    Applies all functions on reconstructions of all the
    values in the fixpoint, and asserts that the result
    is still in the fixpoint. Checks up to depth 2.
    """
    fixpoint = Fixpoint(system)
    values = set(fixpoint.reachable_vectors.values())
    for f in system.problem.functions:
        inputs = [fixpoint.reconstruct(v) for v in values]
        for application in get_applications(f, inputs):
            assert system.eval(application) in values
    for f in system.problem.functions:
        for application in get_applications(
            f,
            itertools.chain(
                *(
                    get_applications(g, [fixpoint.reconstruct(v) for v in values])
                    for g in system.problem.functions
                )
            ),
        ):
            assert system.eval(application) in values


@pytest.mark.skip("TODO")
def test_fixpoint(system: System) -> None:
    fixpoint = Fixpoint(system)

    print()
    print()

    # for i, iteration in enumerate(fixpoint.iterations):
    #     fixpoint_vectors = {
    #         assignment.vector for assignment in system.assignments(iteration.post)
    #     }
    #     manual_vectors = system.reachable_vectors(i)
    #
    #     assert {vec.indices for vec in manual_vectors} <= {vec.indices for vec in fixpoint_vectors}
    #     assert manual_vectors <= fixpoint_vectors

    print(system.problem.constants)

    fixpoint_reachable = indices(fixpoint.reachable_vectors)

    print(fixpoint_reachable)

    fixpoint_vectors = set(fixpoint_reachable.values())

    print(fixpoint_vectors)

    intersection, quorum_of = system.problem.functions
    v1, v2, q2 = system.problem.constants

    q2_transition = fixpoint.transitions[q2.decl()]
    v1_transition = fixpoint.transitions[v1.decl()]
    intersection_transition = fixpoint.transitions[intersection]

    print(f"system vars: {system.output_variables}")
    print(
        f"intersection transition: {system.bdd.to_string(intersection_transition.expression)}"
    )

    _arg_vars, q2_after_false = q2_transition.apply(system.bdd.false)
    print(f"q2 after false: {system.bdd.to_string(q2_after_false)}")
    print(f"--> {[ass.vector.indices for ass in system.assignments(q2_after_false)]}")
    print(
        f"--> {[[e.binary.cube for e in ass.vector.elements] for ass in system.assignments(q2_after_false)]}"
    )

    _arg_vars, v1_after_false = v1_transition.apply(system.bdd.false)
    print(f"v1 after false {system.bdd.to_string(v1_after_false)}")
    print(f"--> {[ass.vector.indices for ass in system.assignments(v1_after_false)]}")
    print(
        f"--> {[[e.binary.cube for e in ass.vector.elements] for ass in system.assignments(v1_after_false)]}"
    )

    _arg_vars, v2_after_false = fixpoint.transitions[v2.decl()].apply(system.bdd.false)
    print(f"v2 after false {system.bdd.to_string(v2_after_false)}")
    print(f"--> {[ass.vector.indices for ass in system.assignments(v2_after_false)]}")
    print(
        f"--> {[[e.binary.cube for e in ass.vector.elements] for ass in system.assignments(v2_after_false)]}"
    )

    arg_vars, after_intersection = intersection_transition.apply(
        q2_after_false, v1_after_false
    )
    print(f"post states {system.bdd.to_string(after_intersection)}")
    print(
        f"--> {[ass.vector.indices for ass in system.assignments(after_intersection)]}"
    )

    bdd = system.bdd

    # print(bdd.to_string(fixpoint.transitions[intersection].expression))

    q2vec = system.eval(q2)
    v1vec = system.eval(v1)

    print(f"{q2}: {q2vec.indices} {system.bdd.to_string(q2vec.cube)}")
    print(f"{v1}: {v1vec.indices} {system.bdd.to_string(v1vec.cube)}")

    term = intersection(q2, v1)
    term_vec = system.eval(term)
    print(f"{term}: {term_vec.indices}")

    # term2 = intersection(v1, q2)
    # term2_vec = system.eval(term2)
    # print(f"{term2}: {term2_vec.indices}")

    print(f"{len(fixpoint)} iterations")
    print(fixpoint_vectors)

    def foo(e: BDDFunction) -> None:
        print(f"--> {[ass.vector.indices for ass in system.assignments(e)]}")

    foo(fixpoint.iterations[0].pre)
    foo(fixpoint.iterations[0].post)
    print(f"===> {fixpoint.reconstruct_all(fixpoint.iterations[0].post)}")
    foo(fixpoint.iterations[1].pre)
    foo(fixpoint.iterations[1].post)
    print(f"===> {fixpoint.reconstruct_all(fixpoint.iterations[1].post)}")
    # foo(fixpoint.iterations[2].pre)
    # foo(fixpoint.iterations[2].post)
    # print(f"===> {fixpoint.reconstruct_all(fixpoint.iterations[2].post)}")

    vecs = {
        ass.vector.indices: ass.vector
        for ass in system.assignments(fixpoint.iterations[1].post)
    }

    vec12 = vecs[(1, 2)]
    vec10 = vecs[(1, 0)]
    vec11 = vecs[(1, 1)]

    print(vec10.indices)
    print(fixpoint.reconstruct(vec10))
    print(vec11.indices)
    print(fixpoint.reconstruct(vec11))
    print(vec12.indices)
    print(fixpoint.reconstruct(vec12))

    print("***")

    assert term_vec.indices in fixpoint_vectors

    m1, m2 = system.models

    m1q2 = m1.universe.elements[1]
    m1v1 = m1.universe.elements[2]
    m2q2 = m2.universe.elements[1]
    m2v1 = m2.universe.elements[0]

    assert q2vec.elements == (m1q2, m2q2)
    assert v1vec.elements == (m1v1, m2v1)

    m1term = intersection(m1q2.value, m1v1.value)
    m1result = m1.eval(m1term)

    m2term = intersection(m2q2.value, m2v1.value)
    m2result = m2.eval(m2term)

    print(f"({m1result.index}, {m2result.index})")

    m1vec = Vector((m1q2, m1v1))
    m2vec = Vector((m2q2, m2v1))

    print("m1")
    print(f"{m1vec.indices} -> {m1result.index}")
    print(bdd.to_string(m1vec.argument_cube))
    print(m1result.binary.cube)
    m1transition = m1vec.argument_cube & bdd.to_expression(m1result.binary.cube)
    print(bdd.to_string(m1transition))

    print("m2")
    print(f"{m2vec.indices} -> {m2result.index}")
    print(bdd.to_string(m2vec.argument_cube))
    print(m2result.binary.cube)
    m2transition = m2vec.argument_cube & bdd.to_expression(m2result.binary.cube)
    print(bdd.to_string(m2transition))

    #
    # for i in range(3):
    #     manual_reachable = indices(system.reachable_vectors(i))
    #
    #     for key, vector in manual_reachable.items():
    #         if vector not in fixpoint_vectors:
    #             print(f"Missing {vector} ({key}) in fixpoint")
    #             print(fixpoint_reachable)
    #             return

    # assert set(manual_reachable.values()) <= set(fixpoint_reachable.values())
