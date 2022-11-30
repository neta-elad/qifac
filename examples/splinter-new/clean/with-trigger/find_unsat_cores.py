from glob import glob

import z3

# set options accotding to dafny generated smt2 files
smt2_prelude = """
(set-option :print-success false)
(set-info :smt-lib-version |2.6|)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
"""
z3.set_param("auto_config", False)
z3.set_param("type_check", True)
z3.set_param("smt.case_split", 3)
z3.set_param("smt.qi.eager_threshold", 100)
z3.set_param("smt.delay_units", True)
z3.set_param("smt.arith.solver", 2)
z3.set_param("smt.arith.nl", False)
z3.set_param("smt.mbqi", False)
z3.set_param("model.compact", False)
z3.set_param("model.v2", True)
z3.set_param("pp.bv_literals", False)


files = glob("oded/?.smt2")
files = [fn for fn in files if "qifac_unsat_core" not in fn]
files = sorted(files, key=lambda x: len(open(x).read()))

if False:
    for fn in files:
        lines = open(fn + "p.smt2").read().splitlines()
        i = 0
        res = []
        while i < len(lines):
            line = lines[i]
            if line.startswith("(assert ") and line.count("(") != line.count(")"):
                assert i + 1 < len(lines)
                assert not lines[i + 1].startswith("(assert ")
                ll = line + "  " + lines[i + 1]
                assert ll.count("(") == ll.count(")"), (i, ll)
                res.append(ll)
                i += 2
            else:
                res.append(line)
                i += 1
        open(fn, "w").write("\n".join(res))
    exit()

for fn in files:
    print()
    print(fn)
    s = z3.Solver()
    s.from_file(fn)
    res = s.check()
    print(f"original file: {res}")
    if res == z3.unknown:
        print(f"    {s.reason_unknown()}")
    elif res == z3.unsat:
        assertions = s.assertions()
        s = z3.Solver()
        bools = [z3.Bool(f"__qifac___flag_{i}") for i in range(len(assertions))]
        s.add(*(z3.Implies(b, a) for a, b in zip(assertions, bools)))
        res = s.check(*bools)
        print(f"    with indicator variabes: {res}")
        if res == z3.unknown:
            print(f"        {s.reason_unknown()}")
        elif res == z3.unsat:
            unsat_core = list(s.unsat_core())
            ii = [int(str(b).split("_")[-1]) for b in unsat_core]
            unsat_core_assertions = [assertions[i] for i in ii]
            print(f"    found unsat core with {len(unsat_core_assertions)} assertions")
            s = z3.Solver()
            s.add(*unsat_core_assertions)
            res = s.check()
            print(
                f"    checking these {len(unsat_core_assertions)} assertions with a new solver: {res}"
            )
            if res == z3.unsat:
                print(f"    OK")
            elif res == z3.unknown:
                print(f"        {s.reason_unknown()}")
            open(fn + ".qifac_unsat_core_to_smt2.smt2", "w").write(
                smt2_prelude + s.to_smt2()
            )
            open(fn + ".qifac_unsat_core.dat", "w").write(repr(ii))

            unsat_core = set(ii)
            lines = open(fn).read().splitlines()
            n = -1
            for i in range(len(lines)):
                if lines[i].startswith("(assert "):
                    n += 1
                    if n not in unsat_core:
                        lines[i] = "; not in unsat core; " + lines[i]
            open(fn + ".qifac_unsat_core.smt2", "w").write("\n".join(lines))
