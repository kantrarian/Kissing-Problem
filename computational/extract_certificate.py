"""
Extract exact certificate from LP solution for K(5) <= 48.

The degree-6 LP gives c_6 ≈ 0, so the certificate is effectively degree 5.
We reconstruct f(t) in standard basis, find its roots, and identify a clean
factored form suitable for Lean formalization.
"""

import numpy as np
from fractions import Fraction
from compute_k5_certificate import gegenbauer_coefficients_d5, eval_gegenbauer, eval_gegenbauer_exact


def main():
    gegenbauer = gegenbauer_coefficients_d5(6)
    
    # LP coefficients from the degree-6 solve (c_6 ≈ 0)
    c_lp = [1.0, 4.9027703810, 10.3053414699, 14.1594217291,
            11.5689020802, 6.0635605823]
    
    print("=" * 70)
    print("STEP 1: Convert LP certificate to standard polynomial")
    print("=" * 70)
    
    # f(t) = sum_k c_k P5_k(t) where P5_k are normalized Gegenbauer for d=5
    # Compute standard coefficients by expanding each P5_k
    
    # P5_0 = 1
    # P5_1 = t
    # P5_2 = (5t^2 - 1)/4 = -1/4 + 5/4 t^2
    # P5_3 = (7t^3 - 3t)/4 = -3/4 t + 7/4 t^3
    # P5_4 = (21t^4 - 14t^2 + 1)/8 = 1/8 - 7/4 t^2 + 21/8 t^4
    # P5_5 = (33t^5 - 30t^3 + 5t)/8 = 5/8 t - 15/4 t^3 + 33/8 t^5
    
    # Standard coefficients a_i (f(t) = sum a_i t^i)
    std = np.zeros(6)  # degree 5
    
    # P5_0 contribution: c_0 * 1
    std[0] += c_lp[0] * 1
    
    # P5_1 contribution: c_1 * t
    std[1] += c_lp[1] * 1
    
    # P5_2 contribution: c_2 * (-1/4 + 5/4 t^2)
    std[0] += c_lp[2] * (-1/4)
    std[2] += c_lp[2] * (5/4)
    
    # P5_3 contribution: c_3 * (-3/4 t + 7/4 t^3)
    std[1] += c_lp[3] * (-3/4)
    std[3] += c_lp[3] * (7/4)
    
    # P5_4 contribution: c_4 * (1/8 - 7/4 t^2 + 21/8 t^4)
    std[0] += c_lp[4] * (1/8)
    std[2] += c_lp[4] * (-7/4)
    std[4] += c_lp[4] * (21/8)
    
    # P5_5 contribution: c_5 * (5/8 t - 15/4 t^3 + 33/8 t^5)
    std[1] += c_lp[5] * (5/8)
    std[3] += c_lp[5] * (-15/4)
    std[5] += c_lp[5] * (33/8)
    
    print("Standard polynomial: f(t) = ", end="")
    terms = []
    for i in range(6):
        if abs(std[i]) > 1e-10:
            terms.append(f"{std[i]:.8f} * t^{i}")
    print(" + ".join(terms))
    
    print(f"\nCoefficients:")
    for i in range(6):
        print(f"  a_{i} = {std[i]:.10f}")
    
    # Verify: f(1) should equal sum(c_lp) ≈ 48
    f1 = sum(std)
    print(f"\nf(1) = {f1:.10f} (should be ~{sum(c_lp):.4f})")
    print(f"f(-1) = {sum(std[i] * (-1)**i for i in range(6)):.10f} (should be ~0)")
    print(f"f(1/2) = {sum(std[i] * (0.5)**i for i in range(6)):.10f} (should be ~0)")
    
    print("\n" + "=" * 70)
    print("STEP 2: Find roots")
    print("=" * 70)
    
    # Use numpy polynomial roots
    poly = np.polynomial.polynomial.Polynomial(std)
    roots = poly.roots()
    
    print("Roots of f(t):")
    real_roots = []
    for r in sorted(roots, key=lambda x: x.real):
        if abs(r.imag) < 1e-6:
            print(f"  t = {r.real:.10f}")
            real_roots.append(r.real)
        else:
            print(f"  t = {r.real:.10f} + {r.imag:.10f}i")
    
    print(f"\n{len(real_roots)} real roots found")
    
    # Check for nice rational approximations
    print("\nRational approximations of real roots:")
    for r in real_roots:
        frac = Fraction(r).limit_denominator(100)
        print(f"  {r:.10f} ~= {frac} = {float(frac):.10f} (err = {abs(r - float(frac)):.2e})")
    
    print("\n" + "=" * 70)
    print("STEP 3: Verify factored form candidates")
    print("=" * 70)
    
    # Check if f(t) = A * (t+1) * (t - r1) * (t - r2) * (t - r3) * (t - r4) * (t - 1/2)
    # where r1, r2, r3, r4 are the other roots
    
    # The leading coefficient gives A
    A = std[5]
    print(f"Leading coefficient (a_5): {A:.10f}")
    print(f"Product of leading terms from roots: (should match a_5)")
    
    # Try explicit factorization
    # We know t=-1 and t=0.5 should be roots (or near-roots)
    # Check:
    for t_val in [-1.0, -0.5, 0.0, 0.5]:
        val = sum(std[i] * t_val**i for i in range(6))
        print(f"  f({t_val}) = {val:.2e}")
    
    print("\n" + "=" * 70)
    print("STEP 4: Try exact Fraction arithmetic")
    print("=" * 70)
    
    # Use exact rational Gegenbauer expansion
    # Scale c_lp so that c_0 = 1 and see if there's a nice rational form
    
    # The bound is f(1)/c_0 = sum(c_k)/c_0
    # For a nice certificate with bound exactly 48:
    # sum(c_k) = 48 * c_0
    
    # Let's try to construct a certificate with EXACTLY bound 48
    # f(t) = (t+1) * g(t) * (t - 1/2) where g(t)^2 is non-negative
    # and f(1)/c_0 = 48
    
    # Actually, let's try a simpler approach.
    # The degree-4 certificate (t+1)(t+1/2)^2(t-1/2) should work for some bound.
    
    print("\nTrying (t+1)(t+1/2)^2(t-1/2) [degree 4]:")
    # (t+1)(t+1/2)^2(t-1/2) = (t+1)(t^2+t+1/4)(t-1/2)
    # = (t+1)(t-1/2)(t^2+t+1/4)
    # Expand: (t^2+t/2-t-1/2)(t^2+t+1/4)
    # = (t^2-1/2)(t^2+t+1/4) + (t/2-1)(t^2+t+1/4)  [wrong approach]
    # Let me just compute numerically
    
    from numpy.polynomial import polynomial as P
    
    p_test = P.polymul(
        P.polymul(np.array([1.0, 1.0]), P.polymul(np.array([0.5, 1.0]), np.array([0.5, 1.0]))),
        np.array([-0.5, 1.0])
    )
    print(f"  Polynomial: {p_test}")
    c_test = poly_to_gegenbauer_exact(p_test, gegenbauer, 4)
    print(f"  Gegenbauer coefficients: {c_test}")
    all_pos = all(c >= -1e-10 for c in c_test[1:])
    bound_test = sum(c_test) / c_test[0] if c_test[0] > 0 else float('inf')
    print(f"  All c_k >= 0: {all_pos}")
    print(f"  Bound: {bound_test:.6f}")
    
    # Try (t+1)(2t+1)^2(t-1/2) [degree 4, different scaling]
    print("\nTrying (t+1)(2t+1)^2(t-1/2) [degree 4]:")
    p_test2 = P.polymul(
        P.polymul(np.array([1.0, 1.0]), P.polymul(np.array([1.0, 2.0]), np.array([1.0, 2.0]))),
        np.array([-0.5, 1.0])
    )
    print(f"  Polynomial: {p_test2}")
    c_test2 = poly_to_gegenbauer_exact(p_test2, gegenbauer, 4)
    print(f"  Gegenbauer coefficients: {c_test2}")
    all_pos2 = all(c >= -1e-10 for c in c_test2[1:])
    bound_test2 = sum(c_test2) / c_test2[0] if c_test2[0] > 0 else float('inf')
    print(f"  All c_k >= 0: {all_pos2}")
    print(f"  Bound: {bound_test2:.6f}")
    
    # Try (t+1)(t+1/2)^2*t*(t-1/2) [degree 5]
    print("\nTrying (t+1)(t+1/2)^2*t*(t-1/2) [degree 5]:")
    p_test3 = P.polymul(
        P.polymul(
            P.polymul(np.array([1.0, 1.0]), P.polymul(np.array([0.5, 1.0]), np.array([0.5, 1.0]))),
            np.array([-0.5, 1.0])
        ),
        np.array([0.0, 1.0])
    )
    print(f"  Polynomial: {p_test3}")
    c_test3 = poly_to_gegenbauer_exact(p_test3, gegenbauer, 5)
    print(f"  Gegenbauer coefficients: {c_test3}")
    all_pos3 = all(c >= -1e-10 for c in c_test3[1:])
    bound_test3 = sum(c_test3) / c_test3[0] if c_test3[0] > 0 else float('inf')
    print(f"  All c_k >= 0: {all_pos3}")
    print(f"  Bound: {bound_test3:.6f}")
    
    # Try (t+1)(t+1/2)^2*t^2*(t-1/2) [degree 6, E8-like]
    print("\nTrying (t+1)(t+1/2)^2*t^2*(t-1/2) [degree 6, E8-like]:")
    p_test4 = P.polymul(
        P.polymul(
            P.polymul(np.array([1.0, 1.0]), P.polymul(np.array([0.5, 1.0]), np.array([0.5, 1.0]))),
            P.polymul(np.array([0.0, 1.0]), np.array([0.0, 1.0]))
        ),
        np.array([-0.5, 1.0])
    )
    print(f"  Polynomial: {p_test4}")
    c_test4 = poly_to_gegenbauer_exact(p_test4, gegenbauer, 6)
    print(f"  Gegenbauer coefficients: {c_test4}")
    all_pos4 = all(c >= -1e-10 for c in c_test4[1:])
    bound_test4 = sum(c_test4) / c_test4[0] if c_test4[0] > 0 else float('inf')
    print(f"  All c_k >= 0: {all_pos4}")
    print(f"  Bound: {bound_test4:.6f}")


def poly_to_gegenbauer_exact(poly_coeffs, gegenbauer, max_k):
    """Convert standard polynomial to Gegenbauer expansion using fine grid."""
    n_grid = 3000
    t_grid = np.linspace(-1, 1, n_grid)
    
    f_vals = np.zeros(n_grid)
    for i in range(len(poly_coeffs)):
        f_vals += float(poly_coeffs[i]) * t_grid**i
    
    P_matrix = np.zeros((n_grid, max_k + 1))
    for j in range(n_grid):
        for k in range(max_k + 1):
            P_matrix[j, k] = eval_gegenbauer(gegenbauer, k, t_grid[j])
    
    c, _, _, _ = np.linalg.lstsq(P_matrix, f_vals, rcond=None)
    return c


if __name__ == "__main__":
    main()
