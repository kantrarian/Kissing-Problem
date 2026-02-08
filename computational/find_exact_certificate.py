"""
Find exact rational certificate for K(5) <= 48.

The degree-6 LP gives bound ~48 with c_6 ≈ 0, so effectively degree 5.
We search for a factored certificate f(t) that:
1. Has f(t) <= 0 on [-1, 1/2] (from its factored form)
2. Has all positive Gegenbauer coefficients
3. Has f(1)/c_0 = 48

Strategy: f(t) = (t+1) * q(t)^2 * (t - 1/2) ensures non-positivity,
where q(t) is a quadratic with real roots in [-1, 1/2].
"""

import numpy as np
from fractions import Fraction
from compute_k5_certificate import gegenbauer_coefficients_d5, eval_gegenbauer, eval_gegenbauer_exact


def poly_to_gegenbauer(poly_coeffs, gegenbauer, max_k):
    """
    Convert a polynomial from standard basis to Gegenbauer expansion.
    
    poly_coeffs: list of coefficients [a_0, a_1, ..., a_n] where f(t) = sum a_i t^i
    gegenbauer: list of Gegenbauer polynomial coefficients
    max_k: maximum Gegenbauer index
    
    Returns Gegenbauer coefficients c_0, ..., c_{max_k} such that
    f(t) = sum_k c_k P_k(t).
    
    Uses least squares on a fine grid (overdetermined system).
    """
    n_grid = 2000
    t_grid = np.linspace(-1, 1, n_grid)
    
    # Evaluate f(t) on grid
    f_vals = np.zeros(n_grid)
    for i, a in enumerate(poly_coeffs):
        f_vals += float(a) * t_grid**i
    
    # Build Gegenbauer matrix
    P_matrix = np.zeros((n_grid, max_k + 1))
    for j in range(n_grid):
        for k in range(max_k + 1):
            P_matrix[j, k] = eval_gegenbauer(gegenbauer, k, t_grid[j])
    
    # Solve least squares
    c, residuals, _, _ = np.linalg.lstsq(P_matrix, f_vals, rcond=None)
    
    return c


def factored_certificate(a, b):
    """
    Build f(t) = (t+1) * (t - a)^2 * (t - b)^2 * (t - 1/2)
    
    where a, b are roots in [-1, 1/2].
    This is degree 6 and satisfies f(t) <= 0 on [-1, 1/2].
    
    Returns standard polynomial coefficients [a_0, a_1, ..., a_6].
    """
    # Multiply out: (t+1)(t-a)^2(t-b)^2(t-1/2)
    # Start with coefficients
    from numpy.polynomial import polynomial as P
    
    p1 = np.array([1, 1])       # t + 1
    p2 = np.array([-a, 1])      # t - a
    p3 = np.array([-b, 1])      # t - b  
    p4 = np.array([-0.5, 1])    # t - 1/2
    
    result = P.polymul(p1, P.polymul(p2, p2))  # (t+1)(t-a)^2
    result = P.polymul(result, P.polymul(p3, p3))  # * (t-b)^2
    result = P.polymul(result, p4)  # * (t-1/2)
    
    return result


def factored_certificate_degree5(a, b):
    """
    Build f(t) = (t+1) * (t - a)^2 * (t - 1/2) * (t - b)
    
    Degree 5. Non-positivity requires checking more carefully.
    For t in [-1, 1/2]:
    - (t+1) >= 0
    - (t-a)^2 >= 0
    - (t-1/2) <= 0
    - (t-b): depends on b
    
    If b <= -1: (t-b) >= 0 on [-1, 1/2], so product <= 0 ✓
    """
    from numpy.polynomial import polynomial as P
    
    p1 = np.array([1, 1])       # t + 1
    p2 = np.array([-a, 1])      # t - a
    p3 = np.array([-0.5, 1])    # t - 1/2
    p4 = np.array([-b, 1])      # t - b
    
    result = P.polymul(p1, P.polymul(p2, p2))  # (t+1)(t-a)^2
    result = P.polymul(result, p3)  # * (t-1/2)
    result = P.polymul(result, p4)  # * (t-b)
    
    return result


def search_degree6_certificate(gegenbauer, target_bound=48):
    """
    Search for factored degree-6 certificate giving bound close to target.
    
    f(t) = (t+1)(t-a)^2(t-b)^2(t-1/2)
    """
    print(f"\nSearching degree-6 factored certificates (target bound = {target_bound})...")
    
    best_result = None
    best_dist = float('inf')
    
    # Grid search over a, b in [-1, 0.5]
    for a in np.linspace(-0.8, 0.4, 200):
        for b in np.linspace(a, 0.4, 200):
            poly = factored_certificate(a, b)
            c = poly_to_gegenbauer(poly, gegenbauer, 6)
            
            # Check all c_k >= 0 for k >= 1
            if any(c[k] < -1e-8 for k in range(1, 7)):
                continue
            
            if c[0] <= 0:
                continue
            
            bound = sum(c) / c[0]
            dist = abs(bound - target_bound)
            
            if dist < best_dist:
                best_dist = dist
                best_result = {
                    'a': a, 'b': b,
                    'poly': poly,
                    'gegenbauer_coeffs': c,
                    'bound': bound,
                    'c0': c[0]
                }
    
    if best_result:
        print(f"  Best: a={best_result['a']:.6f}, b={best_result['b']:.6f}")
        print(f"  Bound: {best_result['bound']:.6f}")
        print(f"  Coefficients: {best_result['gegenbauer_coeffs']}")
    
    return best_result


def search_degree5_certificate(gegenbauer, target_bound=48):
    """
    Search for degree-5 certificates.
    
    f(t) = (t+1)(t-a)^2(t-1/2)(t-b) where b <= -1
    """
    print(f"\nSearching degree-5 factored certificates...")
    
    best_result = None
    best_dist = float('inf')
    
    # a in [-1, 0.5], b <= -1 (ensures non-positivity)
    for a in np.linspace(-0.9, 0.45, 500):
        for b_offset in np.linspace(0, 5, 500):
            b = -1 - b_offset
            poly = factored_certificate_degree5(a, b)
            c = poly_to_gegenbauer(poly, gegenbauer, 5)
            
            if any(c[k] < -1e-8 for k in range(1, 6)):
                continue
            
            if c[0] <= 0:
                continue
            
            bound = sum(c) / c[0]
            dist = abs(bound - target_bound)
            
            if dist < best_dist and bound <= target_bound + 0.01:
                best_dist = dist
                best_result = {
                    'a': a, 'b': b,
                    'poly': poly,
                    'gegenbauer_coeffs': c,
                    'bound': bound
                }
    
    if best_result:
        print(f"  Best: a={best_result['a']:.6f}, b={best_result['b']:.6f}")
        print(f"  Bound: {best_result['bound']:.6f}")
        for k in range(6):
            print(f"    c_{k} = {best_result['gegenbauer_coeffs'][k]:.10f}")
    
    return best_result


def try_known_certificates(gegenbauer):
    """
    Try known certificate forms from the literature.
    
    For d=5, the Levenshtein-type certificate at degree 5 uses the polynomial:
    f(t) = (t+1)(2t+1)^2(t-1/2)  [degree 4]
    or with an additional root for degree 5/6.
    """
    from numpy.polynomial import polynomial as P
    
    print("\n" + "=" * 60)
    print("TRYING KNOWN CERTIFICATE FORMS")
    print("=" * 60)
    
    candidates = [
        # degree 4: (t+1)(2t+1)^2(t-1/2)
        ("(t+1)(2t+1)^2(t-1/2)", lambda: P.polymul(
            P.polymul(np.array([1, 1]), P.polymul(np.array([1, 2]), np.array([1, 2]))),
            np.array([-0.5, 1])
        )),
        # degree 4: (t+1)(t+1/2)^2(t-1/2)
        ("(t+1)(t+1/2)^2(t-1/2)", lambda: P.polymul(
            P.polymul(np.array([1, 1]), P.polymul(np.array([0.5, 1]), np.array([0.5, 1]))),
            np.array([-0.5, 1])
        )),
        # degree 5: (t+1)(t+1/2)^2(t-1/2)*t
        ("(t+1)(t+1/2)^2*t*(t-1/2)", lambda: P.polymul(
            P.polymul(
                P.polymul(np.array([1, 1]), P.polymul(np.array([0.5, 1]), np.array([0.5, 1]))),
                np.array([-0.5, 1])
            ),
            np.array([0, 1])
        )),
        # degree 5: (t+1)^2(t+1/4)^2(t-1/2)
        ("(t+1)^2(t+1/4)^2(t-1/2)", lambda: P.polymul(
            P.polymul(P.polymul(np.array([1, 1]), np.array([1, 1])),
                      P.polymul(np.array([0.25, 1]), np.array([0.25, 1]))),
            np.array([-0.5, 1])
        )),
        # degree 6: (t+1)(t+1/2)^2*t^2*(t-1/2) [E8-like]
        ("(t+1)(t+1/2)^2*t^2*(t-1/2)", lambda: P.polymul(
            P.polymul(
                P.polymul(np.array([1, 1]), P.polymul(np.array([0.5, 1]), np.array([0.5, 1]))),
                P.polymul(np.array([0, 1]), np.array([0, 1]))
            ),
            np.array([-0.5, 1])
        )),
        # degree 6: (t+1)(t+1/3)^2(t-1/5)^2(t-1/2)
        ("(t+1)(t+1/3)^2(t-1/5)^2(t-1/2)", lambda: P.polymul(
            P.polymul(
                P.polymul(np.array([1, 1]), P.polymul(np.array([1/3, 1]), np.array([1/3, 1]))),
                P.polymul(np.array([-1/5, 1]), np.array([-1/5, 1]))
            ),
            np.array([-0.5, 1])
        )),
    ]
    
    for name, make_poly in candidates:
        poly = make_poly()
        degree = len(poly) - 1
        
        # Get Gegenbauer expansion
        c = poly_to_gegenbauer(poly, gegenbauer, degree)
        
        # Check coefficient signs
        all_pos = all(c[k] >= -1e-10 for k in range(1, degree + 1))
        c0_pos = c[0] > 0
        
        # Compute bound
        bound = sum(c) / c[0] if c0_pos else float('inf')
        
        # Check non-positivity on [-1, 1/2]
        t_check = np.linspace(-1, 0.5, 5000)
        f_vals = sum(float(poly[i]) * t_check**i for i in range(len(poly)))
        max_val = np.max(f_vals)
        nonpos = max_val <= 1e-10
        
        print(f"\n{name} (degree {degree}):")
        print(f"  c_k >= 0: {all_pos}, c_0 > 0: {c0_pos}")
        print(f"  f(t) <= 0 on [-1,1/2]: {nonpos} (max={max_val:.2e})")
        if c0_pos:
            print(f"  Bound = {bound:.4f} -> K(5) <= {int(np.ceil(bound - 1e-8))}")
        for k in range(degree + 1):
            print(f"    c_{k} = {c[k]:.8f}")


def refine_with_scipy(gegenbauer, initial_a, initial_b, target_bound=48):
    """Use scipy minimize to refine the factored certificate parameters."""
    from scipy.optimize import minimize
    
    def objective(params):
        a, b = params
        if a < -1 or a > 0.5 or b < -1 or b > 0.5:
            return 1e6
        poly = factored_certificate(a, b)
        c = poly_to_gegenbauer(poly, gegenbauer, 6)
        
        # Penalty for negative coefficients
        penalty = sum(max(0, -c[k]) * 1000 for k in range(1, 7))
        if c[0] <= 0:
            return 1e6
        
        bound = sum(c) / c[0]
        return abs(bound - target_bound) + penalty
    
    result = minimize(objective, [initial_a, initial_b], method='Nelder-Mead',
                     options={'maxiter': 50000, 'xatol': 1e-12, 'fatol': 1e-12})
    
    return result.x


def try_exact_expansion(gegenbauer):
    """
    Directly construct f(t) from LP coefficients and find exact form.
    
    The degree-6 LP gives c_6 ≈ 0, so the certificate is really degree 5.
    We use the LP coefficients to reconstruct f(t) and find its roots.
    """
    print("\n" + "=" * 60)
    print("RECONSTRUCTING CERTIFICATE FROM LP COEFFICIENTS")
    print("=" * 60)
    
    # LP coefficients (degree 6, from the LP solver)
    c_lp = [1.0, 4.9027703810, 10.3053414699, 14.1594217291, 
            11.5689020802, 6.0635605823, 0.0]
    
    # Construct f(t) in standard basis
    n_grid = 200
    t_grid = np.linspace(-1, 1, n_grid)
    
    # f(t) = sum_k c_k P_k(t)
    f_vals = np.zeros(n_grid)
    for k in range(7):
        for j in range(n_grid):
            f_vals[j] += c_lp[k] * eval_gegenbauer(gegenbauer, k, t_grid[j])
    
    # Convert to standard polynomial by fitting
    # f(t) = a_0 + a_1 t + ... + a_5 t^5
    V = np.vander(t_grid, 6, increasing=True)
    std_coeffs, _, _, _ = np.linalg.lstsq(V, f_vals, rcond=None)
    
    print("\nStandard polynomial coefficients:")
    for i, c in enumerate(std_coeffs):
        print(f"  a_{i} = {c:.10f}")
    
    # f(t) in standard form
    poly = np.polynomial.polynomial.Polynomial(std_coeffs)
    
    # Find roots
    roots = poly.roots()
    print(f"\nRoots of f(t):")
    for r in sorted(roots, key=lambda x: x.real):
        if abs(r.imag) < 1e-8:
            print(f"  t = {r.real:.10f}")
        else:
            print(f"  t = {r.real:.10f} + {r.imag:.10f}i")
    
    # Check f(t) at key points
    print(f"\nf(-1) = {np.polynomial.polynomial.polyval(-1, std_coeffs):.10f}")
    print(f"f(0) = {np.polynomial.polynomial.polyval(0, std_coeffs):.10f}")
    print(f"f(0.5) = {np.polynomial.polynomial.polyval(0.5, std_coeffs):.10f}")
    print(f"f(1) = {np.polynomial.polynomial.polyval(1, std_coeffs):.10f}")
    
    # The bound is f(1)/c_0
    f1 = sum(c_lp)
    print(f"\nf(1) from Gegenbauer: {f1:.10f}")
    print(f"Bound = f(1)/c_0 = {f1/c_lp[0]:.10f}")
    
    return std_coeffs, roots


if __name__ == "__main__":
    gegenbauer = gegenbauer_coefficients_d5(12)
    
    # Method 1: Try known certificate forms
    try_known_certificates(gegenbauer)
    
    # Method 2: Reconstruct from LP and find roots
    std_coeffs, roots = try_exact_expansion(gegenbauer)
    
    # Method 3: Search for factored degree-6 certificates
    result6 = search_degree6_certificate(gegenbauer, target_bound=48)
    
    if result6:
        # Refine
        a_ref, b_ref = refine_with_scipy(gegenbauer, result6['a'], result6['b'])
        print(f"\nRefined: a={a_ref:.10f}, b={b_ref:.10f}")
        
        poly = factored_certificate(a_ref, b_ref)
        c = poly_to_gegenbauer(poly, gegenbauer, 6)
        bound = sum(c) / c[0]
        print(f"Refined bound: {bound:.10f}")
        for k in range(7):
            print(f"  c_{k} = {c[k]:.10f}")
    
    # Method 4: Search degree-5 certificates
    result5 = search_degree5_certificate(gegenbauer, target_bound=48)
