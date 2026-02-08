"""Sprint 5.9-D: Statistical analysis of N=41 with 200 restarts"""
import numpy as np
import json
from sprint59c_control_first import (
    random_shell, repair_then_polish, OptParams, min_gap, radial_error
)

def run_n41_statistics(n_restarts: int = 200, seed: int = 0):
    rng = np.random.default_rng(seed)
    params = OptParams()
    R = 1.0
    N_target = 41
    d = 5
    eps_g = 1e-5
    eps_r = 1e-5
    
    results = []
    best_overall = None
    
    print(f"Sprint 5.9-D: N=41 Statistical Analysis ({n_restarts} restarts)")
    print("=" * 60)
    
    for r in range(n_restarts):
        x0 = random_shell(N_target, d=d, R=R, rng=rng)
        out = repair_then_polish(x0, R=R, params=params, eps_g=eps_g, eps_r=eps_r)
        
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
    gaps = [r["best_min_gap"] for r in results]
    gaps = np.array(gaps)
    
    stats = {
        "n_restarts": len(results),
        "certified_count": sum(r["certified"] for r in results),
        "best_min_gap": float(np.max(gaps)),
        "median_min_gap": float(np.median(gaps)),
        "mean_min_gap": float(np.mean(gaps)),
        "std_min_gap": float(np.std(gaps)),
        "quantiles": {
            "q10": float(np.percentile(gaps, 10)),
            "q25": float(np.percentile(gaps, 25)),
            "q50": float(np.percentile(gaps, 50)),
            "q75": float(np.percentile(gaps, 75)),
            "q90": float(np.percentile(gaps, 90)),
        },
        "in_good_basin": int(np.sum(gaps > -0.04)),  # within ~0.04 of feasibility
    }
    
    print("\n" + "=" * 60)
    print("STATISTICS")
    print("=" * 60)
    print(f"  Restarts: {stats['n_restarts']}")
    print(f"  Certified: {stats['certified_count']}")
    print(f"  Best gap: {stats['best_min_gap']:.6f}")
    print(f"  Median gap: {stats['median_min_gap']:.6f}")
    print(f"  Mean gap: {stats['mean_min_gap']:.6f}")
    print(f"  Std gap: {stats['std_min_gap']:.6f}")
    print(f"  In good basin (>-0.04): {stats['in_good_basin']}/{stats['n_restarts']}")
    print(f"  Quantiles: {stats['quantiles']}")
    
    with open("sprint59d_n41_statistics.json", "w") as f:
        json.dump({"stats": stats, "gaps": gaps.tolist()}, f, indent=2)
    
    if best_overall.get("points") is not None:
        np.save("sprint59d_best_N41.npy", best_overall["points"])
    
    return stats, results

if __name__ == "__main__":
    stats, results = run_n41_statistics(n_restarts=200, seed=42)
