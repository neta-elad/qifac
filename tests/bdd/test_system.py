from qifac.search.bdd.system import System


def test_universes(system: System) -> None:
    assert len(system.models) == System.models_amount


def test_axioms(system: System) -> None:
    assert len(system.axioms) == len(system.problem.quantified_assertions)


def test_variables(system: System) -> None:
    assert system.output_variables == {"x⁰₀", "x¹₀", "x²₀", "x²₁"}
    assert system.argument_variables == {
        "₀x⁰₀",
        "₀x¹₀",
        "₀x²₀",
        "₀x²₁",
        "₁x⁰₀",
        "₁x¹₀",
        "₁x²₀",
        "₁x²₁",
        "₂x²₀",
        "₂x¹₀",
        "₂x⁰₀",
        "₂x²₁",
    }
    assert (
        system.element_variables == system.output_variables | system.argument_variables
    )

    assert system.axioms.variables == {"q₀", "q₁", "q₂"}

    assert system.variables == system.element_variables | system.axioms.variables


def test_states(system: System) -> None:
    constants = system.problem.constants
    evaluations = {
        tuple(model.eval(constant) for model in system.models) for constant in constants
    }
    initial_elements = {
        assignment.tuple for assignment in system.assignments(system.initial_states)
    }

    assert evaluations <= initial_elements


def test_vector(system: System) -> None:
    c = next(iter(system.problem.constants))

    vector1 = tuple(model.eval(c) for model in system.models)

    assert system.eval(c).elements == vector1
