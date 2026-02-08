import numpy as np
import json
from dataclasses import dataclass

# -------------------------
# Geometry helpers
# -------------------------

def project_all(points: np.ndarray, radius: float) -> np.ndarray:
    norms = np.linalg.norm(points, axis=1, keepdims=True)
    norms = np.maximum(norms, 1e-12)
    return radius * points / norms

def random_shell(N: int, d: int = 5, R: float = 1.0, rng=None) -> np.ndarray:
    if rng is None:
        rng = np.random.default_rng()
    x = rng.normal(size=(N, d))
    return project_all(x, radius=2.0 * R)

# -------------------------
# Pairwise metrics
# -------------------------

def min_gap(points: np.ndarray, R: float) -> float:
    diff = points[:, None, :] - points[None, :, :]
    dist = np.linalg.norm(diff, axis=2)
    N = dist.shape[0]
    dist[np.arange(N), np.arange(N)] = np.inf
    g = dist - 2.0 * R
    return float(np.min(g))

def radial_error(points: np.ndarray, R: float) -> float:
    target = 2.0 * R
    return float(np.max(np.abs(np.linalg.norm(points, axis=1) - target)))

# -------------------------
# Log-Sum-Exp Max-Min Objective
# -------------------------

def logsumexp_maxmin_and_grad(points: np.ndarray, R: float, tau: float) -> tuple[float, np.ndarray]:
    """
    L = tau * log(sum_{i<j} exp(-gap_ij / tau))
    
    Minimizing L ≈ minimizing max(-gap) ≈ maximizing min(gap)
    """
    N, d = points.shape
    diff = points[:, None, :] - points[None, :, :]          # (N,N,d)
    dist = np.linalg.norm(diff, axis=2) + 1e-12             # (N,N)
    gap = dist - 2.0 * R                                     # (N,N)
    
    # z = -gap/tau (higher z for more overlap)
    z = -gap / max(tau, 1e-12)
    
    # Only use upper triangle (i < j)
    triu_idx = np.triu_indices(N, k=1)
    z_triu = z[triu_idx]
    
    # Numerically stable logsumexp
    z_max = np.max(z_triu)
    exp_z = np.exp(z_triu - z_max)
    sum_exp = np.sum(exp_z)
    L = tau * (z_max + np.log(sum_exp))
    
    # Gradient: dL/dx_i
    # dL/dgap_ij = -softmax(z)_ij = -exp(z_ij) / sum_exp
    # dgap_ij/dx_i = (x_i - x_j) / dist_ij
    
    # Build full softmax matrix (symmetric for convenience)
    softmax_full = np.zeros((N, N))
    softmax_full[triu_idx] = exp_z / sum_exp
    softmax_full = softmax_full + softmax_full.T  # symmetrize
    
    # dL/dgap = -softmax, so dL/dx_i = sum_j (-softmax_ij) * (x_i - x_j) / dist_ij
    coeff = -softmax_full / dist                              # (N,N)
    np.fill_diagonal(coeff, 0.0)
    grad = np.sum(coeff[:, :, None] * diff, axis=1)           # (N,d)
    
    return L, grad

def project_grad_tangent(points: np.ndarray, grad: np.ndarray) -> np.ndarray:
    norms = np.linalg.norm(points, axis=1, keepdims=True) + 1e-12
    xhat = points / norms
    radial = np.sum(grad * xhat, axis=1, keepdims=True) * xhat
    return grad - radial

# -------------------------
# Optimization loop
# -------------------------

@dataclass
class OptParams:
    max_iters: int = 8000
    eta0: float = 0.02
    eta_decay: float = 0.9995
    tau0: float = 0.20
    tau_decay: float = 0.9998
    tau_min: float = 0.005
    stagnation_window: int = 500
    reheat_factor: float = 2.0

def optimize_shell(points: np.ndarray, R: float, params: OptParams, eps_g: float, eps_r: float, rng=None) -> dict:
    radius = 2.0 * R
    x = project_all(points.copy(), radius)
    
    if rng is None:
        rng = np.random.default_rng()

    best = {
        "min_gap": -np.inf,
        "points": x.copy(),
        "iter": 0
    }
    
    eta = params.eta0
    tau = params.tau0
    stagnation_count = 0

    for it in range(params.max_iters):
        g = min_gap(x, R)
        re = radial_error(x, R)

        if g > best["min_gap"]:
            best["min_gap"] = g
            best["points"] = x.copy()
            best["iter"] = it
            stagnation_count = 0
        else:
            stagnation_count += 1

        # Certification check
        if (g >= -eps_g) and (re <= eps_r):
            return {
                "certified": True,
                "best": best,
                "final_points": x,
                "final_min_gap": g,
                "final_rad_err": re,
                "iters": it
            }

        # Reheat on stagnation
        if stagnation_count >= params.stagnation_window:
            tau = min(params.tau0, tau * params.reheat_factor)
            # Add small tangent perturbation
            noise = rng.normal(size=x.shape) * 0.01
            noise_tan = project_grad_tangent(x, noise)
            x = x + noise_tan
            x = project_all(x, radius)
            stagnation_count = 0

        L, grad = logsumexp_maxmin_and_grad(x, R, tau)
        
        # Tangent step + reproject
        grad_tan = project_grad_tangent(x, grad)
        x = x - eta * grad_tan
        x = project_all(x, radius)

        # Anneal
        eta *= params.eta_decay
        tau = max(params.tau_min, tau * params.tau_decay)

    g = min_gap(x, R)
    re = radial_error(x, R)
    return {
        "certified": False,
        "best": best,
        "final_points": x,
        "final_min_gap": g,
        "final_rad_err": re,
        "iters": params.max_iters
    }

# -------------------------
# Falsification matrix search
# -------------------------

def run_falsification_matrix(N_list: list, n_restarts: int, d: int, R: float, 
                              eps_g: float, eps_r: float, seed: int = 0):
    rng = np.random.default_rng(seed)
    params = OptParams()
    
    all_results = {}
    
    for N_target in N_list:
        print(f"\n{'='*60}")
        print(f"Testing N = {N_target}")
        print(f"{'='*60}")
        
        results = []
        best_overall = None
        
        for r in range(n_restarts):
            x0 = random_shell(N_target, d=d, R=R, rng=rng)
            out = optimize_shell(x0, R=R, params=params, eps_g=eps_g, eps_r=eps_r, rng=rng)
            
            rec = {
                "restart": r,
                "certified": bool(out["certified"]),
                "final_min_gap": float(out["final_min_gap"]),
                "final_rad_err": float(out["final_rad_err"]),
                "best_min_gap": float(out["best"]["min_gap"]),
                "best_iter": int(out["best"]["iter"]),
            }
            results.append(rec)
            
            if best_overall is None or rec["best_min_gap"] > best_overall["best_min_gap"]:
                best_overall = rec.copy()
                best_overall["points"] = out["best"]["points"]
            
            if out["certified"]:
                print(f"  *** CERTIFIED at restart {r}! gap = {rec['best_min_gap']:.6f}")
                best_overall = rec.copy()
                best_overall["points"] = out["final_points"]
                break
            
            if (r + 1) % 10 == 0:
                print(f"  Restart {r+1}/{n_restarts}, best_min_gap: {best_overall['best_min_gap']:.6f}")
        
        summary = {
            "N_target": N_target,
            "n_restarts": len(results),
            "certified_any": any(r["certified"] for r in results),
            "best_min_gap": best_overall["best_min_gap"],
            "best_restart": best_overall["restart"],
        }
        
        all_results[N_target] = {
            "summary": summary,
            "runs": results
        }
        
        # Save per-N results
        with open(f"sprint59b_results_N{N_target}.json", "w") as f:
            json.dump(all_results[N_target], f, indent=2)
        
        if best_overall.get("points") is not None:
            np.save(f"sprint59b_best_N{N_target}.npy", best_overall["points"])
        
        print(f"\nN={N_target} Summary: certified={summary['certified_any']}, best_gap={summary['best_min_gap']:.6f}")
    
    return all_results

# -------------------------
# Main
# -------------------------

if __name__ == "__main__":
    # Falsification matrix: N=40 (should work), N=41 (target), N=45 (should fail)
    N_list = [40, 41, 45]
    d = 5
    R = 1.0
    n_restarts = 50
    eps_r = 1e-5
    eps_g = 1e-5
    seed = 42

    print("Sprint 5.9-B: Max-Min Gap Optimizer with Falsification Matrix")
    print(f"Testing: N = {N_list}")
    print(f"Parameters: n_restarts={n_restarts}, eps_r={eps_r}, eps_g={eps_g}")
    
    results = run_falsification_matrix(N_list, n_restarts, d, R, eps_g, eps_r, seed)
    
    # Final summary
    print("\n" + "="*60)
    print("FALSIFICATION MATRIX SUMMARY")
    print("="*60)
    for N in N_list:
        s = results[N]["summary"]
        status = "CERTIFIED" if s["certified_any"] else "FAILED"
        print(f"  N={N:2d}: {status:10s} best_gap={s['best_min_gap']:+.6f}")
    
    # Save combined results
    with open("sprint59b_falsification_matrix.json", "w") as f:
        combined = {str(N): results[N]["summary"] for N in N_list}
        json.dump(combined, f, indent=2)
