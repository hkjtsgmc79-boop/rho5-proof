import sympy as s
import guard_system as g

assert len(g.guards)==35
# Structural sanity checks recorded in the report.
degrees=[s.Poly(x,*g.variables).total_degree() for x in g.guards]
assert degrees[0]==1
assert degrees[26]==24
assert s.Poly(g.g35,*g.variables).total_degree() >= 1
assert s.Poly(g.g36,*g.variables).total_degree() >= 1
print("V26_GUARD_DICTIONARY_PASSED", len(g.guards), "max_degree", max(degrees))
