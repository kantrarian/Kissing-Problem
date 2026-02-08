"""Sprint 5.9-E: Active-Set Polish + Surgery Moves"""
import numpy as np
import json
from dataclasses import dataclass

# Import base functions from 5.9-C
from sprint59c_control_first import (
    project_all, random_shell, min_gap, radial_error,
    overlap_penalty_and_grad, project_grad_tangent, AdamState
)

# -------------------------
# Active-set gradient (D3)
# -------------------------

def get_active_set(points: np.ndarray, R: float, K: int = 150) -> tuple[np.ndarray, np.ndarray]:
    """Get the K worst pairs (smallest gaps) and their gaps."""
    N = points.shape[0]
    diff = points[:, None, :] - points[None, :, :]
    dist = np.linalg.norm(diff, axis=2) + 1e-12
    gap = dist - 2.0 * R
    np.fill_diagonal(gap, np.inf)
    
    # Get upper triangle (i < j)
    triu_idx = np.triu_indices(N, k=1)
    gaps_triu = gap[triu_idx]
    
    # Sort and take K worst
    worst_idx = np.argsort(gaps_triu)[:K]
    worst_pairs = np.array([(triu_idx[0][i], triu_idx[1][i]) for i in worst_idx])
    worst_gaps = gaps_triu[worst_idx]
    
    return worst_pairs, worst_gaps

def activeset_grad(points: np.ndarray, R: float, active_pairs: np.ndarray, tau: float) -> np.ndarray:
    """Compute gradient only on active-set pairs (K worst)."""
    N, d = points.shape
    grad = np.zeros_like(points)
    
    for i, j in active_pairs:
        diff = points[i] - points[j]
        dist = np.linalg.norm(diff) + 1e-12
        gap = dist - 2.0 * R
        
        # softplus penalty
        z = -gap / max(tau, 1e-12)
        sp = np.log1p(np.exp(-abs(z))) + max(z, 0)
        sig = 1.0 / (1.0 + np.exp(-z))
        
        dpen_dgap = (2.0 * sp * sig) * (-1.0 / max(tau, 1e-12))
        
        # Gradient contribution
        grad_contrib = dpen_dgap * diff / dist
        grad[i] += grad_contrib
        grad[j] -= grad_contrib
    
    return grad

# -------------------------
# Surgery moves (D4)
# -------------------------

def surgery_kick(points: np.ndarray, active_pairs: np.ndarray, 
                 kick_strength: float = 0.02, rng=None) -> np.ndarray:
    """Apply tangential kick to points most involved in active set."""
    if rng is None:
        rng = np.random.default_rng()
    
    N = points.shape[0]
    
    # Count overlap degree per point
    overlap_degree = np.zeros(N)
    for i, j in active_pairs[:50]:  # Focus on worst 50
        overlap_degree[i] += 1
        overlap_degree[j] += 1
    
    # Pick 1-3 most stressed points
    worst_points = np.argsort(overlap_degree)[-3:]
    
    # Apply random tangential kick
    kicked = points.copy()
    for p in worst_points:
        noise = rng.normal(size=points.shape[1]) * kick_strength
        noise_tan = project_grad_tangent(kicked[p:p+1], noise.reshape(1, -1))
        kicked[p] += noise_tan.flatten()
    
    return kicked

# -------------------------
# Repair-then-ActiveSet-Polish with Surgery
# -------------------------

@dataclass
class OptParamsE:
    # Repair phase
    repair_iters: int = 10000
    repair_eta: float = 0.01
    repair_tau: float = 0.10
    repair_target: float = -0.01
    
    # Active-set polish phase
    polish_iters: int = 15000
    polish_eta: float = 0.01
    polish_tau: float = 0.05
    active_K: int = 150
    refresh_every: int = 100
    
    # Surgery
    stagnation_window: int = 2000
    surgery_kick: float = 0.03
    max_surgery_attempts: int = 5
    
    # Gradient clipping
    max_step_norm: float = 0.02

def repair_then_activeset_polish(points: np.ndarray, R: float, params: OptParamsE, 
                                   eps_g: float, eps_r: float, rng=None) -> dict:
    if rng is None:
        rng = np.random.default_rng()
    
    radius = 2.0 * R
    x = project_all(points.copy(), radius)
    N, d = x.shape
    
    adam = AdamState((N, d))
    best = {"min_gap": -np.inf, "points": x.copy(), "iter": 0, "phase": "init"}
    
    # === REPAIR PHASE ===
    for it in range(params.repair_iters):
        g = min_gap(x, R)
        re = radial_error(x, R)
        
        if g > best["min_gap"]:
            best["min_gap"] = g
            best["points"] = x.copy()
            best["iter"] = it
            best["phase"] = "repair"
        
        if (g >= -eps_g) and (re <= eps_r):
            return {"certified": True, "best": best, "final_points": x,
                    "final_min_gap": g, "final_rad_err": re, "iters": it, "phase": "repair"}
        
        if g > params.repair_target:
            break
        
        _, grad = overlap_penalty_and_grad(x, R, params.repair_tau)
        grad_tan = project_grad_tangent(x, grad)
        grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
        grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
        
        step = adam.step(grad_tan, params.repair_eta)
        x = x - step
        x = project_all(x, radius)
    
    repair_exit_iter = it
    
    # === ACTIVE-SET POLISH PHASE ===
    adam = AdamState((N, d))
    stagnation_count = 0
    surgery_count = 0
    active_pairs = None
    
    for it in range(params.polish_iters):
        g = min_gap(x, R)
        re = radial_error(x, R)
        
        if g > best["min_gap"]:
            best["min_gap"] = g
            best["points"] = x.copy()
            best["iter"] = repair_exit_iter + it
            best["phase"] = "polish"
            stagnation_count = 0
        else:
            stagnation_count += 1
        
        if (g >= -eps_g) and (re <= eps_r):
            return {"certified": True, "best": best, "final_points": x,
                    "final_min_gap": g, "final_rad_err": re, 
                    "iters": repair_exit_iter + it, "phase": "polish"}
        
        # Refresh active set periodically
        if active_pairs is None or it % params.refresh_every == 0:
            active_pairs, _ = get_active_set(x, R, K=params.active_K)
        
        # Surgery on stagnation
        if stagnation_count >= params.stagnation_window and surgery_count < params.max_surgery_attempts:
            x = surgery_kick(x, active_pairs, params.surgery_kick, rng)
            x = project_all(x, radius)
            
            # Mini-repair after surgery
            for _ in range(1000):
                _, grad = overlap_penalty_and_grad(x, R, params.repair_tau)
                grad_tan = project_grad_tangent(x, grad)
                grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
                grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
                step = adam.step(grad_tan, params.repair_eta)
                x = x - step
                x = project_all(x, radius)
            
            surgery_count += 1
            stagnation_count = 0
            adam = AdamState((N, d))  # Reset Adam
            active_pairs = None  # Force refresh
            continue
        
        # Active-set gradient
        grad = activeset_grad(x, R, active_pairs, params.polish_tau)
        grad_tan = project_grad_tangent(x, grad)
        grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
        grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
        
        step = adam.step(grad_tan, params.polish_eta)
        x = x - step
        x = project_all(x, radius)
    
    g = min_gap(x, R)
    re = radial_error(x, R)
    return {"certified": False, "best": best, "final_points": x,
            "final_min_gap": g, "final_rad_err": re, 
            "iters": params.repair_iters + params.polish_iters, "phase": "polish"}

# -------------------------
# Run N=41 with active-set + surgery
# -------------------------

def run_n41_activeset(n_restarts: int = 200, seed: int = 0):
    rng = np.random.default_rng(seed)
    params = OptParamsE()
    R = 1.0
    N_target = 41
    d = 5
    eps_g = 1e-5
    eps_r = 1e-5
    
    results = []
    best_overall = None
    
    print(f"Sprint 5.9-E: N=41 Active-Set Polish + Surgery ({n_restarts} restarts)")
    print("=" * 60)
    
    for r in range(n_restarts):
        x0 = random_shell(N_target, d=d, R=R, rng=rng)
        out = repair_then_activeset_polish(x0, R=R, params=params, eps_g=eps_g, eps_r=eps_r, rng=rng)
        
        rec = {
            "restart": r,
            "certified": bool(out["certified"]),
            "best_min_gap": float(out["best"]["min_gap"]),
        }
        results.append(rec)
        
        if best_overall is None or rec["best_min_gap"] > best_overall["best_min_gap"]:
            best_overall = rec.copy()
            best_overall["points"] = out["best"]["points"]
        
        if out["certified"]:
            print(f"  *** CERTIFIED at restart {r}! gap = {rec['best_min_gap']:.6f}")
            break
        
        if (r + 1) % 20 == 0:
            print(f"  Restart {r+1}/{n_restarts}, best: {best_overall['best_min_gap']:.6f}")
    
    # Statistics
    gaps = np.array([r["best_min_gap"] for r in results])
    
    stats = {
        "n_restarts": len(results),
        "certified_count": sum(r["certified"] for r in results),
        "best_min_gap": float(np.max(gaps)),
        "median_min_gap": float(np.median(gaps)),
        "mean_min_gap": float(np.mean(gaps)),
        "std_min_gap": float(np.std(gaps)),
        "in_good_basin": int(np.sum(gaps > -0.04)),
    }
    
    print("\n" + "=" * 60)
    print("STATISTICS")
    print("=" * 60)
    print(f"  Restarts: {stats['n_restarts']}")
    print(f"  Certified: {stats['certified_count']}")
    print(f"  Best gap: {stats['best_min_gap']:.6f}")
    print(f"  Median gap: {stats['median_min_gap']:.6f}")
    print(f"  In good basin (>-0.04): {stats['in_good_basin']}/{stats['n_restarts']}")
    
    with open("sprint59e_n41_statistics.json", "w") as f:
        json.dump({"stats": stats, "gaps": gaps.tolist()}, f, indent=2)
    
    if best_overall.get("points") is not None:
        np.save("sprint59e_best_N41.npy", best_overall["points"])
    
    return stats, results

if __name__ == "__main__":
    stats, results = run_n41_activeset(n_restarts=200, seed=42)
