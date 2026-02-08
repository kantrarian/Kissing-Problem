import numpy as np
import json
from dataclasses import dataclass

# -------------------------
# D₅ Polytope Generator (40 vertices for kissing in 5D)
# -------------------------

def d5_shell_points(R: float = 1.0) -> np.ndarray:
    """
    Generate the 40 vertices of the D₅ polytope (demipenteract).
    These form the optimal kissing configuration in 5D.
    
    The vertices are all permutations of (±1, ±1, 0, 0, 0) with an even number of minus signs.
    Scaled to lie on sphere of radius 2R.
    """
    from itertools import permutations, combinations
    
    # Generate all permutations of (1, 1, 0, 0, 0) and sign variants
    base = [1, 1, 0, 0, 0]
    vertices = set()
    
    for perm in permutations(base):
        # Get positions of non-zero elements
        nonzero_pos = [i for i, v in enumerate(perm) if v != 0]
        
        # Generate sign combinations (all 4 variants for D₅ roots)
        for signs in [(1, 1), (-1, -1), (1, -1), (-1, 1)]:
            vertex = list(perm)
            vertex[nonzero_pos[0]] *= signs[0]
            vertex[nonzero_pos[1]] *= signs[1]
            vertices.add(tuple(vertex))
    
    # Convert to numpy array
    points = np.array(list(vertices), dtype=float)
    
    # Scale to radius 2R (current norm is sqrt(2))
    current_norm = np.sqrt(2)
    target_radius = 2.0 * R
    points = points * (target_radius / current_norm)
    
    return points

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
# Smooth overlap penalty (for repair phase)
# -------------------------

def softplus(x: np.ndarray) -> np.ndarray:
    return np.log1p(np.exp(-np.abs(x))) + np.maximum(x, 0)

def sigmoid(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-x))

def overlap_penalty_and_grad(points: np.ndarray, R: float, tau: float) -> tuple[float, np.ndarray]:
    N, d = points.shape
    diff = points[:, None, :] - points[None, :, :]
    dist = np.linalg.norm(diff, axis=2) + 1e-12
    gap = dist - 2.0 * R
    z = (-gap) / max(tau, 1e-12)
    
    sp = softplus(z)
    sig = sigmoid(z)
    
    triu = np.triu(np.ones((N, N), dtype=bool), k=1)
    pen = float(np.sum((sp[triu] ** 2)))
    
    dpen_dgap = (2.0 * sp * sig) * (-1.0 / max(tau, 1e-12))
    np.fill_diagonal(dpen_dgap, 0.0)
    
    coeff = dpen_dgap / dist
    grad = np.sum(coeff[:, :, None] * diff, axis=1)
    
    return pen, grad

# -------------------------
# Max-min (log-sum-exp) objective
# -------------------------

def logsumexp_maxmin_and_grad(points: np.ndarray, R: float, tau: float) -> tuple[float, np.ndarray]:
    N, d = points.shape
    diff = points[:, None, :] - points[None, :, :]
    dist = np.linalg.norm(diff, axis=2) + 1e-12
    gap = dist - 2.0 * R
    z = -gap / max(tau, 1e-12)
    
    triu_idx = np.triu_indices(N, k=1)
    z_triu = z[triu_idx]
    
    z_max = np.max(z_triu)
    exp_z = np.exp(z_triu - z_max)
    sum_exp = np.sum(exp_z)
    L = tau * (z_max + np.log(sum_exp))
    
    softmax_full = np.zeros((N, N))
    softmax_full[triu_idx] = exp_z / sum_exp
    softmax_full = softmax_full + softmax_full.T
    
    coeff = -softmax_full / dist
    np.fill_diagonal(coeff, 0.0)
    grad = np.sum(coeff[:, :, None] * diff, axis=1)
    
    return L, grad

def project_grad_tangent(points: np.ndarray, grad: np.ndarray) -> np.ndarray:
    norms = np.linalg.norm(points, axis=1, keepdims=True) + 1e-12
    xhat = points / norms
    radial = np.sum(grad * xhat, axis=1, keepdims=True) * xhat
    return grad - radial

# -------------------------
# Adam optimizer state
# -------------------------

class AdamState:
    def __init__(self, shape, beta1=0.9, beta2=0.999, eps=1e-8):
        self.m = np.zeros(shape)
        self.v = np.zeros(shape)
        self.beta1 = beta1
        self.beta2 = beta2
        self.eps = eps
        self.t = 0
    
    def step(self, grad: np.ndarray, eta: float) -> np.ndarray:
        self.t += 1
        self.m = self.beta1 * self.m + (1 - self.beta1) * grad
        self.v = self.beta2 * self.v + (1 - self.beta2) * (grad ** 2)
        m_hat = self.m / (1 - self.beta1 ** self.t)
        v_hat = self.v / (1 - self.beta2 ** self.t)
        return eta * m_hat / (np.sqrt(v_hat) + self.eps)

# -------------------------
# Repair-then-Polish optimization
# -------------------------

@dataclass
class OptParams:
    # Repair phase
    repair_iters: int = 10000
    repair_eta: float = 0.01
    repair_tau: float = 0.10
    repair_target: float = -0.01  # Switch to polish when gap > this
    
    # Polish phase
    polish_iters: int = 10000
    polish_eta: float = 0.005
    polish_tau0: float = 0.10
    polish_tau_decay: float = 0.9998
    polish_tau_min: float = 0.005
    
    # Gradient clipping
    max_step_norm: float = 0.02

def repair_then_polish(points: np.ndarray, R: float, params: OptParams, 
                        eps_g: float, eps_r: float) -> dict:
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
        
        # Certification check
        if (g >= -eps_g) and (re <= eps_r):
            return {
                "certified": True,
                "best": best,
                "final_points": x,
                "final_min_gap": g,
                "final_rad_err": re,
                "iters": it,
                "phase": "repair"
            }
        
        # Transition to polish if overlap is small enough
        if g > params.repair_target:
            break
        
        _, grad = overlap_penalty_and_grad(x, R, params.repair_tau)
        grad_tan = project_grad_tangent(x, grad)
        
        # Clip gradient
        grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
        grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
        
        step = adam.step(grad_tan, params.repair_eta)
        x = x - step
        x = project_all(x, radius)
    
    repair_exit_iter = it
    repair_exit_gap = min_gap(x, R)
    
    # === POLISH PHASE ===
    adam = AdamState((N, d))  # Reset Adam
    tau = params.polish_tau0
    
    for it in range(params.polish_iters):
        g = min_gap(x, R)
        re = radial_error(x, R)
        
        if g > best["min_gap"]:
            best["min_gap"] = g
            best["points"] = x.copy()
            best["iter"] = repair_exit_iter + it
            best["phase"] = "polish"
        
        # Certification check
        if (g >= -eps_g) and (re <= eps_r):
            return {
                "certified": True,
                "best": best,
                "final_points": x,
                "final_min_gap": g,
                "final_rad_err": re,
                "iters": repair_exit_iter + it,
                "phase": "polish"
            }
        
        _, grad = logsumexp_maxmin_and_grad(x, R, tau)
        grad_tan = project_grad_tangent(x, grad)
        
        # Clip gradient
        grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
        grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
        
        step = adam.step(grad_tan, params.polish_eta)
        x = x - step
        x = project_all(x, radius)
        
        # Anneal tau only after repair
        tau = max(params.polish_tau_min, tau * params.polish_tau_decay)
    
    g = min_gap(x, R)
    re = radial_error(x, R)
    return {
        "certified": False,
        "best": best,
        "final_points": x,
        "final_min_gap": g,
        "final_rad_err": re,
        "iters": params.repair_iters + params.polish_iters,
        "phase": "polish"
    }

# -------------------------
# Control harness
# -------------------------

def run_control_first(N_list: list, n_restarts: int, d: int, R: float,
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
            # Use D₅ for first restart if N=40
            if N_target == 40 and r == 0:
                x0 = d5_shell_points(R=R)
                print(f"  Restart 0: Using D₅ seed (N={len(x0)})")
            else:
                x0 = random_shell(N_target, d=d, R=R, rng=rng)
            
            out = repair_then_polish(x0, R=R, params=params, eps_g=eps_g, eps_r=eps_r)
            
            rec = {
                "restart": r,
                "certified": bool(out["certified"]),
                "final_min_gap": float(out["final_min_gap"]),
                "final_rad_err": float(out["final_rad_err"]),
                "best_min_gap": float(out["best"]["min_gap"]),
                "best_iter": int(out["best"]["iter"]),
                "best_phase": out["best"]["phase"],
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
            
            if (r + 1) % 5 == 0 or r == 0:
                print(f"  Restart {r+1}/{n_restarts}, best_gap: {best_overall['best_min_gap']:.6f}")
        
        summary = {
            "N_target": N_target,
            "n_restarts": len(results),
            "certified_any": any(r["certified"] for r in results),
            "best_min_gap": best_overall["best_min_gap"],
            "best_restart": best_overall["restart"],
        }
        
        all_results[N_target] = {"summary": summary, "runs": results}
        
        with open(f"sprint59c_results_N{N_target}.json", "w") as f:
            json.dump(all_results[N_target], f, indent=2)
        
        if best_overall.get("points") is not None:
            np.save(f"sprint59c_best_N{N_target}.npy", best_overall["points"])
        
        print(f"\nN={N_target}: certified={summary['certified_any']}, best_gap={summary['best_min_gap']:.6f}")
    
    return all_results

# -------------------------
# Main
# -------------------------

if __name__ == "__main__":
    # First: sanity check D₅
    print("=" * 60)
    print("SANITY CHECK: D₅ Configuration")
    print("=" * 60)
    
    R = 1.0
    d5 = d5_shell_points(R=R)
    print(f"D₅ points: {len(d5)}")
    print(f"D₅ radii: min={np.min(np.linalg.norm(d5, axis=1)):.6f}, max={np.max(np.linalg.norm(d5, axis=1)):.6f}")
    print(f"D₅ min_gap: {min_gap(d5, R):.6f}")
    print(f"D₅ radial_error: {radial_error(d5, R):.6e}")
    
    # Control-first falsification matrix
    N_list = [40, 41, 45]
    n_restarts = 20
    eps_r = 1e-5
    eps_g = 1e-5
    seed = 42
    
    print(f"\nSprint 5.9-C: Control-First Certification")
    print(f"Testing: N = {N_list}")
    print(f"Parameters: n_restarts={n_restarts}, repair+polish=20k iters")
    
    results = run_control_first(N_list, n_restarts, d=5, R=R, eps_g=eps_g, eps_r=eps_r, seed=seed)
    
    # Final summary
    print("\n" + "=" * 60)
    print("FALSIFICATION MATRIX SUMMARY")
    print("=" * 60)
    for N in N_list:
        s = results[N]["summary"]
        status = "CERTIFIED" if s["certified_any"] else "FAILED"
        print(f"  N={N:2d}: {status:10s} best_gap={s['best_min_gap']:+.6f}")
    
    with open("sprint59c_falsification_matrix.json", "w") as f:
        combined = {str(N): results[N]["summary"] for N in N_list}
        json.dump(combined, f, indent=2)
