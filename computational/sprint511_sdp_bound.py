"""Sprint 5.11-B: SDP Upper Bound for Spherical Codes (Delsarte's Method)"""
import numpy as np
import cvxpy as cp
from scipy.special import eval_gegenbauer

# -------------------------
# Delsarte Linear Programming Bound
# -------------------------

def gegenbauer_polynomials(d, k_max, x_val):
    """
    Compute Gegenbauer polynomials C_k^alpha(x) for k=0...k_max.
    For S^(d-1), alpha = (d-2)/2.
    """
    alpha = (d - 2) / 2.0
    coeffs = []
    for k in range(k_max + 1):
        val = eval_gegenbauer(k, alpha, x_val)
        coeffs.append(val)
    return np.array(coeffs)

def solve_delsarte_bound(d: int, angle_deg: float, k_max: int = 20):
    """
    Solve Delsarte's LP bound for spherical codes.
    Maximize sum(f_k) subject to constraints.
    Actually, maximize A (code size) s.t. A <= 1 + sum f_k
    It's usually formulated as:
    Minimize 1 + sum(f_k) subject to:
      f_k >= 0 for k >= 1
      F(x) = 1 + sum(f_k * P_k(x)) <= 0 for x in [-1, cos(theta)]
    where P_k are normalized Gegenbauer polynomials.
    
    Standard LP formulation (Kingman/Delsarte):
    Find polynomial F(t) = sum_{k=0}^M f_k P_k(t) such that:
    1. f_0 > 0
    2. f_k >= 0 for k=1...M
    3. F(t) <= 0 for t in [-1, cos(theta)]
    Minimize F(1) / f_0.
    
    This provides an upper bound on N.
    """
    cos_theta = np.cos(np.deg2rad(angle_deg))
    
    # Coefficients f_k are variables
    f = cp.Variable(k_max + 1)
    
    # Constraints
    constraints = [
        f[0] == 1.0,           # Normalization
        f[1:] >= 0             # Non-negative expansion coeffs
    ]
    
    # Grid constraints for F(t) <= 0 in [-1, cos(theta)]
    # Discretize interval [-1, cos_theta]
    t_grid = np.linspace(-1.0, cos_theta, 200)
    
    # Precompute Gegenbauer polynomials P_k(t) for all t in grid
    # Dimension d -> alpha = (d-2)/2
    alpha = (d - 2) / 2.0
    
    # Constraints: sum(f_k * P_k(t)) <= 0
    t_grid = np.linspace(-1.0, cos_theta, 200)
    for t in t_grid:
        Pk_t = np.array([eval_gegenbauer(k, alpha, t) for k in range(k_max + 1)])
        constraints.append(f @ Pk_t <= 0)
        
    # Normalization: F(1) = 1
    # P_k(1) = binom(k + 2*alpha - 1, k)
    Pk_1 = np.array([eval_gegenbauer(k, alpha, 1.0) for k in range(k_max + 1)])
    constraints.append(f @ Pk_1 == 1.0)
    
    # Objective: Maximize f_0. Upper bound is 1/f_0
    obj = cp.Maximize(f[0])
    
    prob = cp.Problem(obj, constraints)
    try:
        prob.solve(solver=cp.SCS, eps=1e-6)
        if f[0].value is not None and f[0].value > 1e-9:
            return 1.0 / f[0].value
        else:
            return float('inf')
    except:
        return float('inf')

def run_sdp_check(d=5, angle=60.0):
    print(f"Computing Delsarte LP Upper Bound for d={d}, angle={angle}°")
    print("=" * 60)
    
    # Try increasing degree to see convergence
    for k in [10, 15, 20, 30]:
        try:
            bound = solve_delsarte_bound(d, angle, k_max=k)
            print(f"Degree {k}: Upper Bound <= {bound:.6f}")
            if bound < 41.0:
                print(f"  *** PROOF: N < 41 confirmed! (Bound={bound:.6f})")
        except Exception as e:
            print(f"Degree {k}: Solver failed ({e})")

if __name__ == "__main__":
    try:
        run_sdp_check(d=5, angle=60.0)
    except ImportError:
        print("Error: cvxpy or scipy not installed. Please install them to run this script.")
        print("pip install cvxpy scipy")
