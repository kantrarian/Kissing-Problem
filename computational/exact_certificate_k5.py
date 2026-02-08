"""
Compute EXACT rational Gegenbauer expansion of the K(5) <= 48 certificate:

    f(t) = (t + 5/7)^2 * (t + 1/7)^2 * (t - 1/2)

Using exact Fraction arithmetic throughout.
"""

from fractions import Fraction
from compute_k5_certificate import gegenbauer_coefficients_d5, eval_gegenbauer_exact
import json
from pathlib import Path


def poly_multiply_exact(p1, p2):
    """Multiply two polynomials represented as lists of Fractions (lowest degree first)."""
    n = len(p1) + len(p2) - 1
    result = [Fraction(0)] * n
    for i, a in enumerate(p1):
        for j, b in enumerate(p2):
            result[i + j] += a * b
    return result


def poly_eval_exact(coeffs, t):
    """Evaluate polynomial at t (Fraction)."""
    result = Fraction(0)
    for i, c in enumerate(coeffs):
        result += c * (t ** i)
    return result


def main():
    print("=" * 70)
    print("EXACT CERTIFICATE FOR K(5) <= 48")
    print("=" * 70)
    
    # Step 1: Build f(t) = (t + 5/7)^2 * (t + 1/7)^2 * (t - 1/2)
    print("\n--- Step 1: Build polynomial ---")
    
    # (t + 5/7)
    q1 = [Fraction(5, 7), Fraction(1)]
    # (t + 5/7)^2
    q1_sq = poly_multiply_exact(q1, q1)
    # (t + 1/7)
    q2 = [Fraction(1, 7), Fraction(1)]
    # (t + 1/7)^2
    q2_sq = poly_multiply_exact(q2, q2)
    # (t - 1/2)
    q3 = [Fraction(-1, 2), Fraction(1)]
    
    # f(t) = q1^2 * q2^2 * q3
    f = poly_multiply_exact(poly_multiply_exact(q1_sq, q2_sq), q3)
    
    print("f(t) = (t + 5/7)^2 * (t + 1/7)^2 * (t - 1/2)")
    print("Standard form:")
    for i, c in enumerate(f):
        print(f"  a_{i} = {c} = {float(c):.10f}")
    
    # Verify key values
    f_at_1 = poly_eval_exact(f, Fraction(1))
    f_at_neg1 = poly_eval_exact(f, Fraction(-1))
    f_at_half = poly_eval_exact(f, Fraction(1, 2))
    f_at_neg57 = poly_eval_exact(f, Fraction(-5, 7))
    f_at_neg17 = poly_eval_exact(f, Fraction(-1, 7))
    
    print(f"\nf(1) = {f_at_1} = {float(f_at_1):.10f}")
    print(f"f(-1) = {f_at_neg1} = {float(f_at_neg1):.10f}")
    print(f"f(1/2) = {f_at_half}")
    print(f"f(-5/7) = {f_at_neg57}")
    print(f"f(-1/7) = {f_at_neg17}")
    
    # Step 2: Get exact Gegenbauer polynomials
    print("\n--- Step 2: Gegenbauer polynomials ---")
    gegen = gegenbauer_coefficients_d5(5)
    
    for k in range(6):
        print(f"  P5_{k}(t) = ", end="")
        terms = []
        for i, c in enumerate(gegen[k]):
            if c != 0:
                terms.append(f"({c})*t^{i}")
        print(" + ".join(terms))
    
    # Step 3: Compute Gegenbauer expansion using exact inner products
    # For d=5 (lambda = 3/2), the addition formula gives:
    # c_k = (dim P_k) * <f, P_k>_w / <P_k, P_k>_w
    # where the weight is w(t) = (1-t^2)^{(d-3)/2} = (1-t^2) for d=5
    # and dim P_k = (2k+d-2)(k+d-3)! / (k!(d-2)!) for normalized P_k
    
    # Actually, for the normalized Gegenbauer polynomials P_k with P_k(1) = 1:
    # If f(t) = sum_k c_k P_k(t), then
    # c_k = dim(k,d) * integral_{-1}^{1} f(t) P_k(t) (1-t^2)^{(d-3)/2} dt / integral_{-1}^{1} P_k(t)^2 (1-t^2)^{(d-3)/2} dt
    
    # For d=5, lambda = 3/2:
    # dim(k) = (k+1)(2k+3)/3  (the dimension of the space of harmonic polynomials)
    
    # However, it's simpler to just solve the linear system P_k(t_j) c_k = f(t_j)
    # at enough points.
    
    # Since f is degree 5 and we have P_0 through P_5 (also spanning all polys up to degree 5),
    # we can solve this exactly with 6 evaluation points.
    
    print("\n--- Step 3: Exact Gegenbauer expansion ---")
    
    # Choose 6 points (Fraction values for exact arithmetic)
    eval_points = [Fraction(-1), Fraction(-1, 2), Fraction(0), 
                   Fraction(1, 4), Fraction(1, 2), Fraction(1)]
    
    # Build the 6x6 system: sum_k c_k * P_k(t_j) = f(t_j) for j=0..5
    # Matrix M[j][k] = P_k(t_j)
    # RHS b[j] = f(t_j)
    
    n = 6
    M = [[Fraction(0)] * n for _ in range(n)]
    b = [Fraction(0)] * n
    
    for j in range(n):
        t = eval_points[j]
        b[j] = poly_eval_exact(f, t)
        for k in range(n):
            M[j][k] = eval_gegenbauer_exact(gegen, k, t)
    
    print("System Mx = b:")
    for j in range(n):
        row_str = " ".join(f"{float(M[j][k]):8.4f}" for k in range(n))
        print(f"  [{row_str}] | {float(b[j]):10.6f}")
    
    # Solve with exact Gaussian elimination
    c_exact = solve_linear_exact(M, b)
    
    print("\nExact Gegenbauer coefficients:")
    for k in range(n):
        print(f"  c_{k} = {c_exact[k]} = {float(c_exact[k]):.10f}")
    
    # Verify: sum c_k should equal f(1)
    c_sum = sum(c_exact)
    print(f"\nsum(c_k) = {c_sum} = {float(c_sum):.10f}")
    print(f"f(1) = {f_at_1} = {float(f_at_1):.10f}")
    assert c_sum == f_at_1, f"Mismatch: {c_sum} != {f_at_1}"
    print("Verification: sum(c_k) == f(1)  [PASSED]")
    
    # Bound = f(1) / c_0 = sum(c_k) / c_0
    bound = c_sum / c_exact[0]
    print(f"\nBound = f(1)/c_0 = {c_sum}/{c_exact[0]} = {bound} = {float(bound):.6f}")
    print(f"Integer bound: K(5) <= {bound}")
    
    # Verify all c_k >= 0 for k >= 1
    print("\nPositivity check:")
    all_pos = True
    for k in range(1, n):
        pos = c_exact[k] > 0
        all_pos = all_pos and pos
        print(f"  c_{k} = {c_exact[k]} > 0: {pos}")
    print(f"All c_k > 0 (k>=1): {all_pos}")
    
    # Verify reconstruction
    print("\nReconstruction verification at test points:")
    test_points = [Fraction(-1), Fraction(-3, 4), Fraction(-1, 2),
                   Fraction(-1, 4), Fraction(0), Fraction(1, 4), Fraction(1, 2)]
    for t in test_points:
        f_val = poly_eval_exact(f, t)
        recon = sum(c_exact[k] * eval_gegenbauer_exact(gegen, k, t) for k in range(n))
        match = f_val == recon
        print(f"  t={str(t):>5s}: f(t) = {str(f_val):>20s}, recon = {str(recon):>20s}  {'OK' if match else 'MISMATCH'}")
    
    # Step 4: Lean-ready output
    print("\n" + "=" * 70)
    print("LEAN-READY CERTIFICATE DATA")
    print("=" * 70)
    
    print(f"""
-- K(5) <= 48 via Delsarte LP bound
-- Certificate: f(t) = (t + 5/7)^2 * (t + 1/7)^2 * (t - 1/2)
-- Gegenbauer expansion: f(t) = sum_{{k=0}}^5 c_k P5_k(t)
-- where P5_k are normalized Gegenbauer polynomials for d=5 (lambda=3/2)
""")
    
    for k in range(n):
        num = c_exact[k].numerator
        den = c_exact[k].denominator
        print(f"def k5_coeff_{k} : Rat := {num} / {den}  -- = {float(c_exact[k]):.10f}")
    
    print(f"\n-- f(1) = {f_at_1.numerator} / {f_at_1.denominator}")
    print(f"-- c_0 = {c_exact[0].numerator} / {c_exact[0].denominator}")
    print(f"-- bound = f(1) / c_0 = {bound}")
    
    # Save to JSON
    output = {
        'certificate': '(t + 5/7)^2 * (t + 1/7)^2 * (t - 1/2)',
        'dimension': 5,
        'lambda': '3/2',
        'bound': str(bound),
        'bound_float': float(bound),
        'bound_integer': 48,
        'standard_coefficients': [
            {'index': i, 'value': str(f[i]), 'float': float(f[i])} 
            for i in range(len(f))
        ],
        'gegenbauer_coefficients': [
            {'k': k, 'value': str(c_exact[k]), 'numerator': c_exact[k].numerator,
             'denominator': c_exact[k].denominator, 'float': float(c_exact[k])}
            for k in range(n)
        ],
        'f_at_1': str(f_at_1),
        'f_at_neg1': str(f_at_neg1),
        'gegenbauer_polynomials': [
            {'k': k, 'coefficients': [str(c) for c in gegen[k]]}
            for k in range(n)
        ]
    }
    
    out_dir = Path("./sprint518_results")
    out_dir.mkdir(exist_ok=True)
    with open(out_dir / "exact_certificate_k5_48.json", 'w') as fp:
        json.dump(output, fp, indent=2)
    print(f"\nSaved to {out_dir / 'exact_certificate_k5_48.json'}")
    
    return c_exact, bound


def solve_linear_exact(M, b):
    """Solve Mx = b using exact Gaussian elimination with Fractions."""
    n = len(b)
    # Augmented matrix
    aug = [row[:] + [b[i]] for i, row in enumerate(M)]
    
    for col in range(n):
        # Find pivot
        pivot = None
        for row in range(col, n):
            if aug[row][col] != 0:
                pivot = row
                break
        assert pivot is not None, f"Singular matrix at column {col}"
        
        # Swap rows
        aug[col], aug[pivot] = aug[pivot], aug[col]
        
        # Eliminate below
        for row in range(col + 1, n):
            factor = aug[row][col] / aug[col][col]
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    
    # Back-substitution
    x = [Fraction(0)] * n
    for i in range(n - 1, -1, -1):
        x[i] = aug[i][n]
        for j in range(i + 1, n):
            x[i] -= aug[i][j] * x[j]
        x[i] /= aug[i][i]
    
    return x


if __name__ == "__main__":
    c_exact, bound = main()
