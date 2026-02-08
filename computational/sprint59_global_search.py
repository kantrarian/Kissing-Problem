import numpy as np
import json
from dataclasses import dataclass

# -------------------------
# Geometry helpers
# -------------------------

def project_to_sphere(x: np.ndarray, radius: float) -> np.ndarray:
    n = np.linalg.norm(x)
    if n < 1e-12:
        y = np.zeros_like(x)
        y[0] = radius
        return y
    return radius * x / n

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

def pairwise_dist(points: np.ndarray) -> np.ndarray:
    # dist[i,j] = ||x_i - x_j||
    diff = points[:, None, :] - points[None, :, :]
    return np.linalg.norm(diff, axis=2)

def min_gap(points: np.ndarray, R: float) -> float:
    dist = pairwise_dist(points)
    N = dist.shape[0]
    # ignore diagonal
    dist[np.arange(N), np.arange(N)] = np.inf
    g = dist - 2.0 * R
    return float(np.min(g))

def radial_error(points: np.ndarray, R: float) -> float:
    target = 2.0 * R
    return float(np.max(np.abs(np.linalg.norm(points, axis=1) - target)))

# -------------------------
# Smooth overlap penalty + gradient
# -------------------------

def softplus(x: np.ndarray) -> np.ndarray:
    # stable softplus
    # softplus(x)=log(1+exp(x))
    return np.log1p(np.exp(-np.abs(x))) + np.maximum(x, 0)

def sigmoid(x: np.ndarray) -> np.ndarray:
    # stable sigmoid
    return 1.0 / (1.0 + np.exp(-x))

def overlap_penalty_and_grad(points: np.ndarray, R: float, tau: float) -> tuple[float, np.ndarray]:
    """
    penalty = sum_{i<j} softplus((-gap_ij)/tau)^2
    gradient computed for all points (same shape as points)
    """
    N, d = points.shape
    diff = points[:, None, :] - points[None, :, :]          # (N,N,d)
    dist = np.linalg.norm(diff, axis=2) + 1e-12             # (N,N)
    gap = dist - 2.0 * R                                     # (N,N)

    # z = (-gap)/tau, so negative gaps => positive z => penalty grows
    z = (-gap) / max(tau, 1e-12)

    sp = softplus(z)                                         # (N,N)
    sig = sigmoid(z)                                         # (N,N)

    # penalty uses i<j only
    triu = np.triu(np.ones((N, N), dtype=bool), k=1)
    pen = float(np.sum((sp[triu] ** 2)))

    # d/dgap of sp(z)^2 where z=(-gap)/tau:
    # dpen/dgap = 2*sp*sig * d z/dgap = 2*sp*sig * (-1/tau)
    dpen_dgap = (2.0 * sp * sig) * (-1.0 / max(tau, 1e-12))
    # ignore diagonal
    np.fill_diagonal(dpen_dgap, 0.0)

    # dgap/dx_i = (x_i - x_j) / dist
    # grad_i = sum_j dpen_dgap[i,j] * (x_i - x_j)/dist[i,j]
    coeff = dpen_dgap / dist                                  # (N,N)
    grad = np.sum(coeff[:, :, None] * diff, axis=1)           # (N,d)

    # IMPORTANT: penalty sums i<j, but we used symmetric matrices.
    # Using symmetric dpen_dgap works because each pair contributes to i and j with opposite sign via diff.

    return pen, grad

def project_grad_tangent(points: np.ndarray, grad: np.ndarray) -> np.ndarray:
    # subtract radial component per point
    norms = np.linalg.norm(points, axis=1, keepdims=True) + 1e-12
    xhat = points / norms
    radial = np.sum(grad * xhat, axis=1, keepdims=True) * xhat
    return grad - radial

# -------------------------
# Optimization loop
# -------------------------

@dataclass
class OptParams:
    max_iters: int = 5000
    eta0: float = 0.01
    eta_decay: float = 0.999
    tau0: float = 0.30
    tau_decay: float = 0.9995
    tau_min: float = 0.01

def optimize_shell(points: np.ndarray, R: float, params: OptParams, eps_g: float, eps_r: float) -> dict:
    radius = 2.0 * R
    x = project_all(points.copy(), radius)

    best = {
        "min_gap": -np.inf,
        "penalty": np.inf,
        "points": x.copy(),
        "iter": 0
    }

    eta = params.eta0
    tau = params.tau0

    for it in range(params.max_iters):
        # feasibility check (projected points only)
        g = min_gap(x, R)
        re = radial_error(x, R)

        if g > best["min_gap"]:
            best["min_gap"] = g
            best["points"] = x.copy()
            best["iter"] = it

        if (g >= -eps_g) and (re <= eps_r):
            return {
                "certified": True,
                "best": best,
                "final_points": x,
                "final_min_gap": g,
                "final_rad_err": re,
                "iters": it
            }

        pen, grad = overlap_penalty_and_grad(x, R, tau)
        if pen < best["penalty"]:
            best["penalty"] = pen

        # tangent step + reproject
        grad_tan = project_grad_tangent(x, grad)
        x = x - eta * grad_tan
        x = project_all(x, radius)

        # anneal
        eta *= params.eta_decay
        tau = max(params.tau_min, tau * params.tau_decay)

    # not certified
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
# Global search
# -------------------------

def global_search(N_target: int, d: int, R: float, n_restarts: int, eps_g: float, eps_r: float, seed: int = 0):
    rng = np.random.default_rng(seed)
    params = OptParams()

    results = []
    best_overall = None

    for r in range(n_restarts):
        x0 = random_shell(N_target, d=d, R=R, rng=rng)
        out = optimize_shell(x0, R=R, params=params, eps_g=eps_g, eps_r=eps_r)

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
            best_overall = rec | {"points": out["best"]["points"]}

        # early stop if any certified
        if out["certified"]:
            best_overall = rec | {"points": out["final_points"]}
            break

        # Progress update every 10 restarts
        if (r + 1) % 10 == 0:
            print(f"  Restart {r+1}/{n_restarts}, best_min_gap so far: {best_overall['best_min_gap']:.6f}")

    return results, best_overall

# -------------------------
# Main
# -------------------------

if __name__ == "__main__":
    N_target = 41
    d = 5
    R = 1.0
    n_restarts = 200
    eps_r = 1e-5
    eps_g = 1e-5
    seed = 0

    print(f"Sprint 5.9-A: Global Search for N={N_target} on S^{d-1}")
    print(f"Parameters: n_restarts={n_restarts}, eps_r={eps_r}, eps_g={eps_g}")
    print("=" * 60)

    results, best = global_search(N_target, d, R, n_restarts, eps_g, eps_r, seed=seed)

    summary = {
        "N_target": N_target,
        "n_restarts": n_restarts,
        "eps_r": eps_r,
        "eps_g": eps_g,
        "certified_any": any(r["certified"] for r in results),
        "best_min_gap": best["best_min_gap"],
        "best_restart": best["restart"],
    }

    with open(f"sprint59_results_N{N_target}.json", "w") as f:
        json.dump({"summary": summary, "runs": results}, f, indent=2)

    # Save best configuration for later certification / analysis
    np.save(f"sprint59_best_N{N_target}.npy", best["points"])

    print("=" * 60)
    print("SUMMARY:")
    print(json.dumps(summary, indent=2))
