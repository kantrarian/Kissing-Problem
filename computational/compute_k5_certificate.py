"""
Sprint 5.18 Phase 1: Delsarte LP Certificate Discovery for K(5)
================================================================

Finds the tightest Delsarte LP upper bound for the kissing number in dimension 5.

The Delsarte LP bound uses:
  - Normalized Gegenbauer polynomials P_k for d=5 (lambda = 3/2)
  - Certificate polynomial f(t) = sum_k c_k * P_k(t)
  - Constraints: c_k >= 0 (k >= 1), f(t) <= 0 on [-1, 1/2]
  - Bound: f(1) / c_0 = (sum_k c_k) / c_0

Known bounds: 40 <= tau_5 <= 44
Classical Delsarte LP gives tau_5 <= 48 (basic)
This script searches for the tightest LP bound across polynomial degrees.
"""

import numpy as np
from fractions import Fraction
from scipy.optimize import linprog
import json
from pathlib import Path


# =============================================================================
# GEGENBAUER POLYNOMIALS FOR d=5 (lambda = 3/2)
# =============================================================================

def gegenbauer_coefficients_d5(max_degree):
    """
    Compute normalized Gegenbauer polynomial coefficients for d=5 (lambda=3/2).
    
    Uses the recurrence relation for ultraspherical polynomials C_k^lambda(t):
      C_0(t) = 1
      C_1(t) = 2*lambda*t
      (k+1) C_{k+1}(t) = 2(k+lambda) t C_k(t) - (k+2*lambda-1) C_{k-1}(t)
    
    Then normalizes: P_k(t) = C_k(t) / C_k(1)  so that P_k(1) = 1.
    
    Returns list of polynomial coefficient arrays (highest degree first for np.polyval).
    """
    lam = Fraction(3, 2)  # lambda = (d-2)/2 = (5-2)/2 = 3/2
    
    # Store as lists of Fraction coefficients (lowest degree first internally)
    # C_0 = [1]
    # C_1 = [0, 2*lam] = [0, 3]
    
    polys = []
    
    # C_0 = 1
    C_prev_prev = [Fraction(1)]
    polys.append(C_prev_prev[:])
    
    if max_degree < 1:
        return _normalize_polys(polys)
    
    # C_1 = 2*lambda*t = 3t
    C_prev = [Fraction(0), 2 * lam]
    polys.append(C_prev[:])
    
    for k in range(1, max_degree):
        # (k+1) C_{k+1}(t) = 2(k+lambda) t C_k(t) - (k+2*lambda-1) C_{k-1}(t)
        k_frac = Fraction(k)
        
        coeff_a = 2 * (k_frac + lam)       # coefficient of t * C_k
        coeff_b = k_frac + 2 * lam - 1     # coefficient of C_{k-1}
        denom = k_frac + 1                  # divide by (k+1)
        
        # t * C_k: shift coefficients up by one degree
        tCk = [Fraction(0)] + C_prev[:]
        
        # Compute (k+1) C_{k+1} = coeff_a * t*C_k - coeff_b * C_{k-1}
        new_len = len(tCk)
        C_new = [Fraction(0)] * new_len
        
        for i in range(len(tCk)):
            C_new[i] += coeff_a * tCk[i]
        for i in range(len(C_prev_prev)):
            C_new[i] -= coeff_b * C_prev_prev[i]
        
        # Divide by (k+1)
        C_new = [c / denom for c in C_new]
        
        polys.append(C_new[:])
        C_prev_prev = C_prev[:]
        C_prev = C_new[:]
    
    return _normalize_polys(polys)


def _normalize_polys(polys):
    """Normalize so P_k(1) = 1 and convert to evaluation-ready format."""
    normalized = []
    for coeffs in polys:
        # Evaluate at t=1: sum of all coefficients
        val_at_1 = sum(coeffs)
        assert val_at_1 != 0, f"Gegenbauer polynomial is zero at t=1"
        
        # Normalize
        norm_coeffs = [c / val_at_1 for c in coeffs]
        
        # Verify P_k(1) = 1
        assert sum(norm_coeffs) == Fraction(1), f"Normalization failed"
        
        normalized.append(norm_coeffs)
    
    return normalized


def eval_gegenbauer(coeffs_list, k, t):
    """Evaluate P_k(t) given coefficient list (lowest degree first)."""
    coeffs = coeffs_list[k]
    result = 0.0
    for i, c in enumerate(coeffs):
        result += float(c) * (t ** i)
    return result


def eval_gegenbauer_exact(coeffs_list, k, t_frac):
    """Evaluate P_k(t) exactly using Fraction arithmetic."""
    coeffs = coeffs_list[k]
    result = Fraction(0)
    for i, c in enumerate(coeffs):
        result += c * (t_frac ** i)
    return result


# =============================================================================
# DELSARTE LP SOLVER
# =============================================================================

def solve_delsarte_lp(d, max_degree, n_grid=2000, verbose=True):
    """
    Solve the Delsarte LP for the kissing number upper bound.
    
    Decision variables: c_0, c_1, ..., c_D  (Gegenbauer coefficients)
    
    Minimize: sum_k c_k  (which equals f(1) since P_k(1) = 1)
    Subject to:
      c_0 = 1  (normalization)
      c_k >= 0 for k = 1, ..., D
      f(t_j) <= 0 for all t_j in [-1, 1/2]  (grid points)
    
    The bound is then f(1)/c_0 = sum_k c_k.
    """
    D = max_degree
    n_vars = D + 1  # c_0, c_1, ..., c_D
    
    # Get Gegenbauer polynomials
    gegenbauer = gegenbauer_coefficients_d5(D)
    
    if verbose:
        print(f"\nSolving Delsarte LP for d={d}, degree={D}")
        print(f"  Gegenbauer polynomials computed (lambda=3/2)")
    
    # Grid points in [-1, 1/2]
    t_grid = np.linspace(-1.0, 0.5, n_grid)
    
    # Precompute P_k(t_j) matrix
    P_matrix = np.zeros((n_grid, n_vars))
    for j in range(n_grid):
        for k in range(n_vars):
            P_matrix[j, k] = eval_gegenbauer(gegenbauer, k, t_grid[j])
    
    # LP: minimize c^T @ 1  (i.e., sum of all c_k)
    # But c_0 = 1 (fixed), so we optimize over c_1, ..., c_D
    # and the objective is 1 + sum_{k=1}^{D} c_k
    
    # Variables: c_1, c_2, ..., c_D  (D variables)
    n_opt = D  # c_1 through c_D
    
    # Objective: minimize sum c_k for k=1..D
    c_obj = np.ones(n_opt)
    
    # Inequality constraints: f(t_j) <= 0 for each grid point
    # f(t_j) = c_0 * P_0(t_j) + sum_{k=1}^D c_k * P_k(t_j)
    # = P_0(t_j) + sum_{k=1}^D c_k * P_k(t_j)  (since c_0 = 1)
    # So: sum_{k=1}^D c_k * P_k(t_j) <= -P_0(t_j) = -1
    
    A_ub = P_matrix[:, 1:]  # Columns for c_1..c_D
    b_ub = -P_matrix[:, 0]  # = -1 for each row (since P_0 = 1)
    
    # Bounds: c_k >= 0 for k = 1, ..., D
    bounds = [(0, None)] * n_opt
    
    # Solve
    result = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    
    if not result.success:
        if verbose:
            print(f"  LP failed: {result.message}")
        return None
    
    # Extract coefficients
    c_opt = np.zeros(n_vars)
    c_opt[0] = 1.0  # c_0 = 1 (normalization)
    c_opt[1:] = result.x
    
    # Bound = f(1) / c_0 = sum_k c_k / 1 = sum_k c_k
    bound = np.sum(c_opt)
    
    if verbose:
        print(f"  LP bound: {bound:.6f}")
        print(f"  Coefficients:")
        for k in range(n_vars):
            print(f"    c_{k} = {c_opt[k]:.10f}")
    
    return {
        'degree': D,
        'bound': bound,
        'bound_ceil': int(np.ceil(bound - 1e-8)),  # Integer bound
        'coefficients': c_opt,
        'gegenbauer': gegenbauer,
        'success': True
    }


def rationalize_certificate(result, gegenbauer, verbose=True):
    """
    Try to find exact rational coefficients for the certificate.
    
    Uses continued fraction approximation to find simple rationals.
    """
    from fractions import Fraction
    
    c_opt = result['coefficients']
    D = result['degree']
    
    if verbose:
        print(f"\nRationalizing certificate (degree {D})...")
    
    # Try to rationalize each coefficient
    c_rational = []
    for k in range(D + 1):
        # Try denominators up to a reasonable limit
        frac = Fraction(c_opt[k]).limit_denominator(100000)
        c_rational.append(frac)
        if verbose:
            print(f"  c_{k} = {float(c_opt[k]):.12f} -> {frac} = {float(frac):.12f}")
    
    # Compute exact bound with rational coefficients
    bound_exact = sum(c_rational)
    if verbose:
        print(f"  Exact bound: {bound_exact} = {float(bound_exact):.6f}")
        print(f"  Integer bound: ceil({float(bound_exact)}) = {int(np.ceil(float(bound_exact) - 1e-10))}")
    
    # Verify non-positivity on [-1, 1/2] with rational coefficients
    t_check = np.linspace(-1.0, 0.5, 10000)
    max_val = -np.inf
    for t in t_check:
        val = sum(float(c_rational[k]) * eval_gegenbauer(gegenbauer, k, t) for k in range(D + 1))
        max_val = max(max_val, val)
    
    if verbose:
        print(f"  Max f(t) on [-1, 1/2]: {max_val:.2e}")
        if max_val <= 1e-10:
            print(f"  Non-positivity: VERIFIED")
        else:
            print(f"  Non-positivity: FAILED (max = {max_val})")
    
    return c_rational, bound_exact


# =============================================================================
# CERTIFICATE POLYNOMIAL CONSTRUCTION
# =============================================================================

def find_factored_certificate(d, target_bound, max_degree=8, verbose=True):
    """
    Search for a certificate polynomial in factored form.
    
    For the kissing number, good certificates often have the form:
    f(t) = (t+1)^a * (t-1/2) * p(t)
    
    where the roots at t=-1 and t=1/2 ensure f(t) <= 0 on [-1, 1/2].
    """
    if verbose:
        print(f"\nSearching for factored certificate (target bound={target_bound})...")
    
    # The E8 certificate was: (t+1)(t+1/2)^2 * t^2 * (t-1/2)
    # For d=5, we try similar structures
    
    # Try: f(t) = (t+1)^a * (t - 1/2) * product of (t - r_i)^2 terms
    # where r_i are in [-1, 1/2] to keep f(t) <= 0
    
    # Placeholder - the LP solution already gives us the certificate
    pass


# =============================================================================
# MAIN
# =============================================================================

def print_gegenbauer_table(max_degree=8):
    """Print the normalized Gegenbauer polynomials for d=5."""
    gegenbauer = gegenbauer_coefficients_d5(max_degree)
    
    print("\nNormalized Gegenbauer Polynomials for d=5 (lambda=3/2)")
    print("=" * 70)
    
    for k, coeffs in enumerate(gegenbauer):
        # Format as polynomial string
        terms = []
        for i, c in enumerate(coeffs):
            if c == 0:
                continue
            if i == 0:
                terms.append(f"{c}")
            elif i == 1:
                terms.append(f"{c}*t")
            else:
                terms.append(f"{c}*t^{i}")
        
        poly_str = " + ".join(terms) if terms else "0"
        print(f"  P5_{k}(t) = {poly_str}")
        
        # Verify P_k(1) = 1
        val = eval_gegenbauer_exact(gegenbauer, k, Fraction(1))
        print(f"    P5_{k}(1) = {val}")
    
    return gegenbauer


def main():
    print("=" * 80)
    print("SPRINT 5.18 PHASE 1: DELSARTE LP CERTIFICATE FOR K(5)")
    print("=" * 80)
    
    # Step 1: Print Gegenbauer polynomials
    gegenbauer = print_gegenbauer_table(12)
    
    # Step 2: Sweep polynomial degrees
    print("\n" + "=" * 80)
    print("DELSARTE LP BOUND SWEEP")
    print("=" * 80)
    
    results = {}
    for degree in [4, 6, 8, 10, 12]:
        result = solve_delsarte_lp(d=5, max_degree=degree, n_grid=5000)
        if result and result['success']:
            results[degree] = result
    
    # Step 3: Find tightest bound
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    
    print(f"\n{'Degree':>8} {'LP Bound':>12} {'Integer':>10}")
    print("-" * 35)
    for deg in sorted(results.keys()):
        r = results[deg]
        print(f"{deg:>8} {r['bound']:>12.6f} {r['bound_ceil']:>10}")
    
    # Best result
    best_deg = min(results.keys(), key=lambda d: results[d]['bound'])
    best = results[best_deg]
    print(f"\nTightest LP bound: {best['bound']:.6f} (degree {best_deg})")
    print(f"Integer upper bound: K(5) <= {best['bound_ceil']}")
    
    # Step 4: Rationalize the best certificate
    print("\n" + "=" * 80)
    print("CERTIFICATE RATIONALIZATION")
    print("=" * 80)
    
    c_rational, bound_exact = rationalize_certificate(
        best, gegenbauer_coefficients_d5(best_deg)
    )
    
    # Step 5: Generate Lean-ready output
    print("\n" + "=" * 80)
    print("LEAN-READY OUTPUT")
    print("=" * 80)
    
    print(f"\n-- Gegenbauer polynomials for d=5 (lambda=3/2)")
    print(f"-- Degree: {best_deg}")
    print(f"-- Bound: K(5) <= {best['bound_ceil']}")
    print(f"\n-- Coefficients (normalized so c_0 = 1):")
    for k in range(best_deg + 1):
        print(f"--   c_{k} = {c_rational[k]}")
    
    # Save results
    output_dir = Path("./sprint518_results")
    output_dir.mkdir(exist_ok=True)
    
    save_data = {
        'dimension': 5,
        'lambda': '3/2',
        'best_degree': best_deg,
        'best_bound': float(best['bound']),
        'integer_bound': best['bound_ceil'],
        'coefficients_float': [float(c) for c in best['coefficients']],
        'coefficients_rational': [str(c) for c in c_rational],
        'bound_exact': str(bound_exact),
        'all_results': {
            str(deg): {
                'degree': deg,
                'bound': float(results[deg]['bound']),
                'bound_ceil': results[deg]['bound_ceil']
            }
            for deg in results
        }
    }
    
    with open(output_dir / "k5_certificate.json", 'w') as f:
        json.dump(save_data, f, indent=2)
    print(f"\nResults saved to {output_dir / 'k5_certificate.json'}")
    
    # Also save Gegenbauer polynomials for Lean
    gegen_data = {}
    gegen = gegenbauer_coefficients_d5(best_deg)
    for k in range(best_deg + 1):
        gegen_data[f"P5_{k}"] = {
            'coefficients': [str(c) for c in gegen[k]],
            'degree': k
        }
    
    with open(output_dir / "gegenbauer_d5.json", 'w') as f:
        json.dump(gegen_data, f, indent=2)
    print(f"Gegenbauer data saved to {output_dir / 'gegenbauer_d5.json'}")
    
    return results, c_rational, bound_exact


if __name__ == "__main__":
    results, c_rational, bound_exact = main()
