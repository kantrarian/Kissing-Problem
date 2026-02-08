"""Sprint 5.10-B: Symmetry-Breaking Seeds for N=41"""
import numpy as np
import json
from sprint59c_control_first import (
    d5_shell_points, repair_then_polish, OptParams, 
    project_all, min_gap, radial_error
)

# -------------------------
# D4 Generator (24 points in 4D, lifted to 5D)
# -------------------------
def d4_shell_points(R: float = 1.0) -> np.ndarray:
    """
    Generate 24 vertices of D4 root system.
    Permutations of (±1, ±1, 0, 0).
    Lifted to 5D by appending 0.
    """
    from itertools import permutations
    
    # 4D coordinates
    base = [1, 1, 0, 0]
    vertices = set()
    
    for perm in permutations(base):
        nonzero_pos = [i for i, v in enumerate(perm) if v != 0]
        for signs in [(1, 1), (1, -1), (-1, 1), (-1, -1)]:
            vertex = list(perm)
            vertex[nonzero_pos[0]] *= signs[0]
            vertex[nonzero_pos[1]] *= signs[1]
            vertices.add(tuple(vertex))
            
    points_4d = np.array(list(vertices), dtype=float)
    
    # Lift to 5D: (x, y, z, w) -> (x, y, z, w, 0)
    N = points_4d.shape[0]
    points_5d = np.zeros((N, 5))
    points_5d[:, :4] = points_4d
    
    # Scale to radius 2R
    # Current norm is sqrt(2)
    current_norm = np.sqrt(2)
    target_radius = 2.0 * R
    points_5d = points_5d * (target_radius / current_norm)
    
    return points_5d

# -------------------------
# Seeding strategies
# -------------------------
def seed_d5_plus_1(R: float, rng) -> np.ndarray:
    """40 points from D5, 1 random point."""
    d5 = d5_shell_points(R) # 40 points
    random_pt = rng.normal(size=(1, 5))
    
    # Project random point
    norm = np.linalg.norm(random_pt)
    random_pt = random_pt * (2.0 * R / norm)
    
    return np.vstack([d5, random_pt])

def seed_d4_plus_17(R: float, rng) -> np.ndarray:
    """24 points from D4 (in hyperplane), 17 random points."""
    d4 = d4_shell_points(R) # 24 points
    random_pts = rng.normal(size=(17, 5))
    
    # Project random points
    norms = np.linalg.norm(random_pts, axis=1, keepdims=True)
    random_pts = random_pts * (2.0 * R / norms)
    
    return np.vstack([d4, random_pts])

# -------------------------
# Experiment runner
# -------------------------
def run_seeded_experiment(strategy_name: str, seed_func, n_restarts: int = 20, seed: int = 42):
    rng = np.random.default_rng(seed)
    R = 1.0
    eps_g = 1e-5
    eps_r = 1e-5
    params = OptParams(repair_iters=5000, polish_iters=8000) # Slightly shorter
    
    print(f"\nRunning Strategy: {strategy_name} ({n_restarts} restarts)")
    print("=" * 60)
    
    results = []
    best_overall = None
    
    for r in range(n_restarts):
        x0 = seed_func(R, rng)
        
        # Add small noise to symmetric part to allow breaking?
        # Ideally we want to *start* symmetric and let optimizer break it if needed.
        # But D5 is a local min. If we don't shake it, points might not move.
        # Let's add tiny noise to everything.
        noise = rng.normal(size=x0.shape) * 0.01
        x0 = project_all(x0 + noise, 2.0*R)
        
        out = repair_then_polish(x0, R, params, eps_g, eps_r)
        
        rec = {
            "restart": r,
            "certified": bool(out["certified"]),
            "best_min_gap": float(out["best"]["min_gap"]),
        }
        results.append(rec)
        
        if best_overall is None or rec["best_min_gap"] > best_overall["best_min_gap"]:
            best_overall = rec.copy()
            best_overall["points"] = out["best"]["points"]
            
        print(f"  Restart {r+1}/{n_restarts}: best_gap={rec['best_min_gap']:.6f} {'[CERTIFIED]' if out['certified'] else ''}")
        
    # Stats
    gaps = np.array([r["best_min_gap"] for r in results])
    print(f"\nSummary for {strategy_name}:")
    print(f"  Best: {np.max(gaps):.6f}")
    print(f"  Median: {np.median(gaps):.6f}")
    print(f"  Certified: {sum(r['certified'] for r in results)}/{n_restarts}")
    
    return results, best_overall

if __name__ == "__main__":
    # D5 + 1
    res_d5, best_d5 = run_seeded_experiment("D5 + 1 Random", seed_d5_plus_1, n_restarts=20)
    
    # D4 + 17
    res_d4, best_d4 = run_seeded_experiment("D4 + 17 Random", seed_d4_plus_17, n_restarts=20)
    
    # Save results
    summary = {
        "D5_plus_1": {
            "best_gap": float(np.max([r["best_min_gap"] for r in res_d5])),
            "certified": any(r["certified"] for r in res_d5)
        },
        "D4_plus_17": {
            "best_gap": float(np.max([r["best_min_gap"] for r in res_d4])),
            "certified": any(r["certified"] for r in res_d4)
        }
    }
    
    with open("sprint510b_results.json", "w") as f:
        json.dump(summary, f, indent=2)
        
    print("\nTotal Experiment Complete.")
