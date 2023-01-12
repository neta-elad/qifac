from typing import List, Tuple

import z3

from .problem import Problem
from .utils import cast_relation


def consensus() -> Tuple[Problem, List[z3.ExprRef]]:
    S = z3.DeclareSort("S")
    node = S
    quorum = S
    value = S

    member = cast_relation(z3.Function("member", node, quorum, z3.BoolSort()))
    intersection = z3.Function("intersection", quorum, quorum, node)
    vote = cast_relation(z3.Function("vote", node, value, z3.BoolSort()))
    decided = cast_relation(z3.Function("decided", value, z3.BoolSort()))
    quorum_of_decided = z3.Function("quorum_of_decided", value, quorum)

    n = z3.Const("n", node)
    v = z3.Const("v", value)
    v1 = z3.Const("v1", value)
    v2 = z3.Const("v2", value)
    z3.Const("q", quorum)
    q1 = z3.Const("q1", quorum)
    q2 = z3.Const("q2", quorum)

    qf_assertions = [
        decided(v1),
        v1 != v2,
    ]

    forall_assertions = [
        z3.ForAll([q1, q2], member(intersection(q1, q2), q1)),
        z3.ForAll([q1, q2], member(intersection(q1, q2), q2)),
        z3.ForAll([n, v1, v2], z3.Implies(z3.And(vote(n, v1), vote(n, v2)), v1 == v2)),
        z3.ForAll(
            [v, n],
            z3.Implies(
                decided(v), z3.Implies(member(n, quorum_of_decided(v)), vote(n, v))
            ),
        ),
        z3.ForAll([n], z3.Implies(member(n, q2), vote(n, v2))),
    ]

    problem = Problem(
        {S},
        {v1, v2, q2},
        {intersection, quorum_of_decided},
        {member, vote, decided},
        qf_assertions,
        forall_assertions,
    )

    return problem, [
        v1,
        v2,
        quorum_of_decided(v1),
        q2,
        intersection(quorum_of_decided(v1), q2),
    ]


def many_sorted_consensus() -> Tuple[Problem, List[z3.ExprRef]]:
    node = z3.DeclareSort("node")
    quorum = z3.DeclareSort("quorum")
    value = z3.DeclareSort("value")

    member = cast_relation(z3.Function("member", node, quorum, z3.BoolSort()))
    intersection = z3.Function("intersection", quorum, quorum, node)
    vote = cast_relation(z3.Function("vote", node, value, z3.BoolSort()))
    decided = cast_relation(z3.Function("decided", value, z3.BoolSort()))
    quorum_of_decided = z3.Function("quorum_of_decided", value, quorum)

    n = z3.Const("n", node)
    v = z3.Const("v", value)
    v1 = z3.Const("v1", value)
    v2 = z3.Const("v2", value)
    z3.Const("q", quorum)
    q1 = z3.Const("q1", quorum)
    q2 = z3.Const("q2", quorum)

    qf_assertions = [
        decided(v1),
        v1 != v2,
    ]

    forall_assertions = [
        z3.ForAll([q1, q2], member(intersection(q1, q2), q1)),
        z3.ForAll([q1, q2], member(intersection(q1, q2), q2)),
        z3.ForAll([n, v1, v2], z3.Implies(z3.And(vote(n, v1), vote(n, v2)), v1 == v2)),
        z3.ForAll(
            [v, n],
            z3.Implies(
                decided(v), z3.Implies(member(n, quorum_of_decided(v)), vote(n, v))
            ),
        ),
        z3.ForAll([n], z3.Implies(member(n, q2), vote(n, v2))),
    ]

    problem = Problem(
        {node, quorum, value},
        {v1, v2, q2},
        {intersection, quorum_of_decided},
        {member, vote, decided},
        qf_assertions,
        forall_assertions,
    )

    return problem, [
        v1,
        v2,
        quorum_of_decided(v1),
        q2,
        intersection(quorum_of_decided(v1), q2),
    ]
