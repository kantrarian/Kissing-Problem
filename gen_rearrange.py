#!/usr/bin/env python3
"""
General-purpose rearrangement lemma generator for PSD6 cross-terms.
Parses goal states after delta collapse and generates ring lemmas.

Usage: python gen_rearrange.py < goal_text
  Or: edit the GOAL variable below and run.
"""

import re
import sys
from collections import Counter

# For BB: each term has x.ofLp and y.ofLp factors
# Parse patterns like:
# x.ofLp x_1 * y.ofLp x_1 * x.ofLp x_2 * y.ofLp x_2 * x.ofLp x_3 * y.ofLp x_3 * x.ofLp x_4 * y.ofLp x_4

def parse_factor(s):
    """Parse a factor like 'x.ofLp x_1' or 'y.ofLp x_2'"""
    s = s.strip()
    m = re.match(r'([xy])\.ofLp (x_\d+)', s)
    if m:
        return (m.group(1), m.group(2))  # ('x', 'x_1') or ('y', 'x_2')
    return None

def parse_term(line):
    """Parse a line of the goal into a list of (vec, idx) factors.
    Returns (factors, num_free_vars) or None if unparsable."""
    line = line.strip().rstrip(' +')
    # Split by ' * '
    parts = line.split(' * ')
    factors = []
    for p in parts:
        p = p.strip().strip('()')
        f = parse_factor(p)
        if f:
            factors.append(f)
    return factors if factors else None

def canonical_form(factors, var_map):
    """Given factors, determine the canonical RHS form.

    Factors are (vec, idx) pairs where vec is 'x' or 'y'.

    Strategy:
    1. Group by index
    2. For each index, determine what vectors use it:
       - If both x and y: it's a "paired" index → (x_i * y_i)
       - If only x (appears 2+): it's an "x-squared" index → (x_i * x_i)
       - If only y (appears 2+): it's a "y-squared" index → (y_i * y_i)
    3. The RHS is the product of all such groups.
    """
    # Map idx to list of vectors
    idx_vecs = {}
    for vec, idx in factors:
        mapped_idx = var_map.get(idx, idx)
        if mapped_idx not in idx_vecs:
            idx_vecs[mapped_idx] = []
        idx_vecs[mapped_idx].append(vec)

    rhs_parts = []
    for idx in sorted(idx_vecs.keys()):
        vecs = sorted(idx_vecs[idx])
        if vecs == ['x', 'y']:
            rhs_parts.append(f'(x.ofLp {idx} * y.ofLp {idx})')
        elif vecs == ['x', 'x']:
            rhs_parts.append(f'(x.ofLp {idx} * x.ofLp {idx})')
        elif vecs == ['y', 'y']:
            rhs_parts.append(f'(y.ofLp {idx} * y.ofLp {idx})')
        elif vecs == ['x', 'x', 'y', 'y']:
            rhs_parts.append(f'(x.ofLp {idx} * x.ofLp {idx})')
            rhs_parts.append(f'(y.ofLp {idx} * y.ofLp {idx})')
        elif vecs == ['x', 'x', 'x', 'y']:
            # x^3 * y - unusual but possible
            rhs_parts.append(f'(x.ofLp {idx} * x.ofLp {idx})')
            rhs_parts.append(f'(x.ofLp {idx} * y.ofLp {idx})')
        elif vecs == ['x', 'y', 'y', 'y']:
            rhs_parts.append(f'(y.ofLp {idx} * y.ofLp {idx})')
            rhs_parts.append(f'(x.ofLp {idx} * y.ofLp {idx})')
        else:
            # General case: just pair them up
            for i in range(0, len(vecs), 2):
                if i + 1 < len(vecs):
                    rhs_parts.append(f'({vecs[i]}.ofLp {idx} * {vecs[i+1]}.ofLp {idx})')
                else:
                    rhs_parts.append(f'{vecs[i]}.ofLp {idx}')

    return ' * '.join(rhs_parts)

def build_lhs(factors, var_map):
    """Build the LHS string from factors."""
    parts = []
    for vec, idx in factors:
        mapped_idx = var_map.get(idx, idx)
        parts.append(f'{vec}.ofLp {mapped_idx}')
    return ' * '.join(parts)

def get_free_vars(factors, var_map):
    """Get the sorted unique mapped variable names."""
    seen = set()
    for _, idx in factors:
        seen.add(var_map.get(idx, idx))
    return sorted(seen)

def generate_lemmas(goal_text, lemma_prefix='r'):
    """Parse goal text and generate unique rearrangement lemmas."""
    lines = goal_text.strip().split('\n')

    # Parse all terms
    terms = []
    current_line = ''
    for line in lines:
        line = line.strip()
        if not line:
            continue
        current_line += ' ' + line
        if line.endswith('+'):
            continue
        # Complete term
        factors = parse_term(current_line)
        if factors:
            terms.append(factors)
        current_line = ''
    # Handle last line
    if current_line.strip():
        factors = parse_term(current_line)
        if factors:
            terms.append(factors)

    print(f"Parsed {len(terms)} terms")

    # Map goal variables (x_1, x_2, ...) to universal names (a, b, c, d, e, ...)
    var_names = 'abcdefghijklmnop'

    seen_patterns = set()
    unique_lemmas = []

    for factors in terms:
        # Get unique indices in order of first appearance
        seen = []
        for _, idx in factors:
            if idx not in seen:
                seen.append(idx)
        var_map = {idx: var_names[i] for i, idx in enumerate(seen)}

        # Build LHS key for dedup
        lhs_key = tuple((v, var_map.get(i, i)) for v, i in factors)
        if lhs_key in seen_patterns:
            continue
        seen_patterns.add(lhs_key)

        # Build LHS and RHS
        lhs = build_lhs(factors, var_map)
        rhs = canonical_form(factors, var_map)
        free_vars = get_free_vars(factors, var_map)

        unique_lemmas.append((lhs, rhs, free_vars))

    print(f"Unique patterns: {len(unique_lemmas)}")

    # Generate Lean code
    lemma_names = []
    for i, (lhs, rhs, free_vars) in enumerate(unique_lemmas):
        name = f'{lemma_prefix}{i+1}'
        lemma_names.append(name)
        var_decl = ' '.join(free_vars)
        print(f"  have {name} : ∀ {var_decl} : Fin 8,")
        print(f"      {lhs} =")
        print(f"      {rhs} := by intros; ring")

    # Generate simp_rw line
    names_str = ', '.join(lemma_names)
    print(f"\n  -- simp_rw line:")
    print(f"  simp_rw [{names_str}]")

    return unique_lemmas

if __name__ == '__main__':
    # Read from stdin or use embedded goal
    if not sys.stdin.isatty():
        goal = sys.stdin.read()
    else:
        print("Paste goal text (end with Ctrl+D or Ctrl+Z):")
        goal = sys.stdin.read()

    generate_lemmas(goal)
