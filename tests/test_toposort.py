from py2many.toposort_modules import TopologicalSorter


def test_basic_dag():
    # A -> B -> C
    graph = {"C": ["B"], "B": ["A"], "A": []}
    ts = TopologicalSorter(graph)
    order = list(ts.static_order())
    assert order == ["A", "B", "C"]


def test_deterministic_order():
    # A, B are independent
    # A, B -> C
    graph = {"C": ["A", "B"], "A": [], "B": []}
    ts = TopologicalSorter(graph)
    order = list(ts.static_order())
    # Should be sorted: A, B then C
    assert order == ["A", "B", "C"]


def test_simple_cycle():
    # A -> B -> A
    # The implementation selects min(active_nodes) when blocked.
    # 'A' < 'B', so 'A' should be picked first to break the cycle.
    graph = {"A": ["B"], "B": ["A"]}
    ts = TopologicalSorter(graph)
    order = list(ts.static_order())
    assert order == ["A", "B"]


def test_complex_cycle():
    # A -> C, B -> A, B -> D, C -> B
    # Wait, my previous manual trace had A -> C, B -> {A, D}, C -> B.
    # Let's use that one.
    # D -> []
    # A -> [C]
    # C -> [B]
    # B -> [A, D]
    graph = {"A": ["C"], "B": ["A", "D"], "C": ["B"], "D": []}
    ts = TopologicalSorter(graph)
    order = list(ts.static_order())
    # Trace:
    # 1. D is ready. Yield D. done(D) -> B in_degree becomes 1 (A).
    # 2. No one ready. min(A,B,C) is A. Yield A. done(A) -> B in_degree becomes 0.
    # 3. B is ready. Yield B. done(B) -> C in_degree becomes 0.
    # 4. C is ready. Yield C.
    assert order == ["D", "A", "B", "C"]


def test_stability_multiple_readies():
    # A, C, B independent. Should be sorted A, B, C
    graph = {"A": [], "B": [], "C": []}
    ts = TopologicalSorter(graph)
    order = list(ts.static_order())
    assert order == ["A", "B", "C"]


def test_disjoint_graphs():
    # (A -> B) and (C -> D)
    graph = {"B": ["A"], "A": [], "D": ["C"], "C": []}
    ts = TopologicalSorter(graph)
    order = list(ts.static_order())
    # A and C are ready first. Sorted: A, C.
    # Then B and D become ready. Sorted: B, D.
    assert order == ["A", "C", "B", "D"]
