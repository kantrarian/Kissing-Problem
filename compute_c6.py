from fractions import Fraction
from itertools import combinations

n = 8

def e1(a):
    return Fraction(1) if a == 0 else Fraction(0)

def delta(a, b):
    return Fraction(1) if a == b else Fraction(0)

def pair_partitions(lst):
    if len(lst) == 0:
        yield []
        return
    first = lst[0]
    for i in range(1, len(lst)):
        pair = (first, lst[i])
        rest = lst[1:i] + lst[i+1:]
        for pp in pair_partitions(rest):
            yield [pair] + pp

def trace_levels(x, i1, i2, i3, i4):
    x6_tr = Fraction(0)
    l1_tr = Fraction(0)
    l2_tr = Fraction(0)
    l3_tr = Fraction(0)
    for m in range(n):
        idx = (i1, i2, i3, i4, m, m)
        xterm = Fraction(1)
        for k in range(6):
            xterm *= x(idx[k])
        x6_tr += xterm

        for di, dj in combinations(range(6), 2):
            prod = delta(idx[di], idx[dj])
            for k in range(6):
                if k != di and k != dj:
                    prod *= x(idx[k])
            l1_tr += prod

        for xp in combinations(range(6), 2):
            remaining = sorted(set(range(6)) - set(xp))
            r = remaining
            parts = [((r[0],r[1]),(r[2],r[3])), ((r[0],r[2]),(r[1],r[3])), ((r[0],r[3]),(r[1],r[2]))]
            for (d1a,d1b),(d2a,d2b) in parts:
                l2_tr += x(idx[xp[0]])*x(idx[xp[1]])*delta(idx[d1a],idx[d1b])*delta(idx[d2a],idx[d2b])

        for pp in pair_partitions(list(range(6))):
            val = Fraction(1)
            for (a, b) in pp:
                val *= delta(idx[a], idx[b])
            l3_tr += val

    return x6_tr, l1_tr, l2_tr, l3_tr

# Use e1 and also e12 = (1/sqrt2, 1/sqrt2, 0,...,0) -- but we need rationals.
# Instead, use more tuples with e1.
tuples = [(0,0,0,0), (0,0,1,1), (1,1,1,1), (1,1,2,2)]
for t in tuples:
    x6, l1, l2, l3 = trace_levels(e1, *t)
    print(f"Trace at {t}: x6={x6}, L1={l1}, L2={l2}, L3={l3}")
    print(f"  Equation: {x6} - a1*{l1} + a2*{l2} - a3*{l3} = 0")

# Equations:
# (0000): 1 - 22*a1 + 87*a2 - 36*a3 = 0
# (0011): -a1 + 15*a2 - 12*a3 = 0
# (1111): ?
# (1122): ?

print()
print("Solving system:")
# From (0000): 1 - 22a1 + 87a2 - 36a3 = 0 ... (I)
# From (0011): -a1 + 15a2 - 12a3 = 0 ... (II)
# From (1111) and (1122): get more equations

# Actually, the trace-free condition must hold for ALL unit vectors x,
# not just e1. The 3 unknowns should be determined by the condition
# that the trace vanishes AS A TENSOR (i.e., for all index tuples AND all unit x).
# For e1, the vanishing condition gives equations involving x-level types:
# - x^4 type: coefficient of x(i1)x(i2)x(i3)x(i4)
# - x^2*delta type: coefficient of x(i1)x(i2)*delta(i3,i4)
# - delta^2 type: coefficient of delta(i1,i2)*delta(i3,i4)
# Each of these must vanish separately.

# The x^4 equation: 1 - a1*(trace of L1 restricted to x^4 terms) = 0
# From my analysis: trace of 15 L1 terms at x^4 level = 16 (for n=8)
# => 1 - 16*a1 = 0 => a1 = 1/16

# But the (0000) trace for e1 mixes all levels. Let me extract the level
# equations from the numerical data.

# With e1:
# (0000): the only x^4 term at (0000) is x(0)^4 = 1.
#         x^2*delta terms at (0000): delta(0,0)*x(0)^2 = 1 (type delta(i,j) with i=j, x=0)
#         delta^2 terms: delta(0,0)*delta(0,0) = 1
# The trace equations for e1 combine these levels weighted by e1 values.

# The (1111) trace with e1 should involve only delta^2 terms (since e1(1)=0).
x6_1111, l1_1111, l2_1111, l3_1111 = trace_levels(e1, 1,1,1,1)
print(f"(1111): 0 - a1*{l1_1111} + a2*{l2_1111} - a3*{l3_1111} = 0")

# (1122):
x6_1122, l1_1122, l2_1122, l3_1122 = trace_levels(e1, 1,1,2,2)
print(f"(1122): 0 - a1*{l1_1122} + a2*{l2_1122} - a3*{l3_1122} = 0")

# Now solve the 3-equation system:
# (0000): 1 - 22*a1 + 87*a2 - 36*a3 = 0  ... (I)
# (0011): -a1 + 15*a2 - 12*a3 = 0          ... (II)
# (1111): -a1_1111*a1 + a2_1111*a2 - a3_1111*a3 = 0  ... (III)

# Let me just use numpy-style solving
from fractions import Fraction

# Build coefficient matrix from the trace equations
eqs = []
for t in [(0,0,0,0), (0,0,1,1), (1,1,1,1), (1,1,2,2)]:
    x6, l1, l2, l3 = trace_levels(e1, *t)
    # x6 - a1*l1 + a2*l2 - a3*l3 = 0
    # => a1*l1 - a2*l2 + a3*l3 = x6
    eqs.append((l1, -l2, l3, x6))

print("\nLinear system (a1*L1 - a2*L2 + a3*L3 = rhs):")
for i, (c1, c2, c3, rhs) in enumerate(eqs):
    print(f"  {c1}*a1 + ({c2})*a2 + {c3}*a3 = {rhs}")

# Solve using Gaussian elimination with fractions
# Equations:
# 22*a1 - 87*a2 + 36*a3 = 1
# a1 - 15*a2 + 12*a3 = 0
# ?*a1 - ?*a2 + ?*a3 = 0
# ?*a1 - ?*a2 + ?*a3 = 0

A = [[eqs[i][j] for j in range(3)] for i in range(4)]
b = [eqs[i][3] for i in range(4)]

# Use first 3 equations (skip trivial ones)
# Eq 0: 22*a1 - 87*a2 + 36*a3 = 1
# Eq 1: 1*a1 - 15*a2 + 12*a3 = 0
# Eq 2: from (1111)
# Eq 3: from (1122)

# Print all equations
for i in range(4):
    print(f"Eq{i}: {A[i][0]}*a1 + {A[i][1]}*a2 + {A[i][2]}*a3 = {b[i]}")

# If eq2 and eq3 give 0=0, we need another approach.
# The issue is that for e1, tuples with all nonzero indices (like 1111)
# might give degenerate equations.

# Let me try with a DIFFERENT unit vector to get more equations.
# Use x = (1/2, 1/2, 1/2, 1/2, 0, 0, 0, 0) -- not unit! ||x||^2 = 1
# Actually ||x||^2 = 4*(1/2)^2 = 1. Yes, unit!
def x4(a):
    return Fraction(1, 2) if a < 4 else Fraction(0)

print("\nUsing x = (1/2,1/2,1/2,1/2,0,0,0,0):")
for t in [(0,0,0,0), (0,0,1,1), (0,1,2,3)]:
    x6, l1, l2, l3 = trace_levels(x4, *t)
    print(f"  Trace at {t}: {x6} - a1*{l1} + a2*{l2} - a3*{l3} = 0")
