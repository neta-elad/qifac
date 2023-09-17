from qifac.search.bdd.fixpoint import Fixpoint
from qifac.search.bdd.instantiations import Instantiations


def test_ins(system):
    inss = Instantiations(Fixpoint(system))
    print("\n")
    print(inss.all_false_instantiations(1))
    print(inss.all_false_instantiations(2))
    print("\n")
