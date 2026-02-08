#!/usr/bin/env python3
"""Generate rearrangement lemmas for sum_AC by parsing the goal state."""

import re

# Raw goal state from the Lean output (concatenated, whitespace-normalized)
goal = r"""
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_2) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_2) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * x.ofLp x_3 * (y.ofLp x_1 * y.ofLp x_2) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * x.ofLp x_2 * (y.ofLp x_1 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * x.ofLp x_3 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_3 * x.ofLp x_2 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_3 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * x.ofLp x_3 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * x.ofLp x_3 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_3 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_3 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * x.ofLp x_3 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * x.ofLp x_2 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * x.ofLp x_1 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_3 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * x.ofLp x_2 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * x.ofLp x_3 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4) +
x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_3 * y.ofLp x_4)
"""

# Parse each term
term_pat = re.compile(
    r'x\.ofLp (x_\d) \* x\.ofLp (x_\d) \* x\.ofLp (x_\d) \* x\.ofLp (x_\d) \* x\.ofLp (x_\d) \* x\.ofLp (x_\d) \* \(y\.ofLp (x_\d) \* y\.ofLp (x_\d)\)'
)

terms = []
for line in goal.strip().split('\n'):
    line = line.strip().rstrip(' +')
    m = term_pat.match(line)
    if m:
        x_indices = [m.group(i) for i in range(1, 7)]
        y_pair = (m.group(7), m.group(8))
        terms.append((x_indices, y_pair))

print(f"Parsed {len(terms)} terms")

# For each term, the x-indices use variables from the y-pair and doubled variables.
# Variables in x_indices: count occurrences
# y-pair variables appear once, doubled variables appear twice.

# Generate lemma for each term
# Map x_1 -> a, x_2 -> b, x_3 -> c, x_4 -> d
var_map = {'x_1': 'a', 'x_2': 'b', 'x_3': 'c', 'x_4': 'd'}

seen_patterns = set()
unique_lemmas = []

for x_indices, y_pair in terms:
    # Convert to variable names
    xi = tuple(var_map[v] for v in x_indices)
    yp = tuple(var_map[v] for v in y_pair)

    # The LHS pattern
    lhs_key = (xi, yp)
    if lhs_key in seen_patterns:
        continue
    seen_patterns.add(lhs_key)

    # Figure out which variables are doubled (appear 2x in x_indices)
    from collections import Counter
    counts = Counter(xi)
    doubled = sorted([v for v, c in counts.items() if c == 2])
    singles = sorted([v for v, c in counts.items() if c == 1])

    assert set(singles) == set(yp), f"Singles {singles} != y-pair {yp} for {xi}"

    # Build LHS string
    lhs_parts = [f'x.ofLp {v}' for v in xi]
    lhs = ' * '.join(lhs_parts) + f' *\n      (y.ofLp {yp[0]} * y.ofLp {yp[1]})'

    # Build RHS string: (x_yi * y_yi) for each y-pair var, then (x_dj * x_dj) for doubled
    rhs_parts = []
    for v in yp:
        rhs_parts.append(f'(x.ofLp {v} * y.ofLp {v})')
    for v in doubled:
        rhs_parts.append(f'(x.ofLp {v} * x.ofLp {v})')
    rhs = ' * '.join(rhs_parts)

    unique_lemmas.append((lhs, rhs, xi, yp))

print(f"Unique patterns: {len(unique_lemmas)}")

# Output the Lean code
print("\n-- Rearrangement lemmas for sum_AC")
lemma_names = []
for i, (lhs, rhs, xi, yp) in enumerate(unique_lemmas):
    name = f'r{i+1}'
    lemma_names.append(name)
    print(f"  have {name} : forall a b c d : Fin 8,")
    print(f"      {lhs} =")
    print(f"      {rhs} := by intros; ring")

# Output the simp_rw line
names_str = ', '.join(lemma_names)
print(f"\n  -- Apply all rearrangements, then factor and substitute")
print(f"  simp_rw [{names_str}, factor4, hxn, <- hs]")
print(f"  ring")
