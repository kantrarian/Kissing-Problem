"""Sprint 5.17: Basin Widening & Hybrid Seeding (v2)"""
import numpy as np
import time
import json
from dataclasses import dataclass
from itertools import combinations, permutations, product

# Import core geometry/optimizer helpers
from sprint59c_control_first import (
    project_all, min_gap, radial_error,
    overlap_penalty_and_grad, logsumexp_maxmin_and_grad,
    project_grad_tangent, AdamState, OptParams,
    d5_shell_points
)

# -----------------------------------------------------
# 1. Structured Data & Known Configs
# -----------------------------------------------------

KISSING_NUMBERS = {
    4: {"tau": 24, "status": "Proven", "symmetry": "24-Cell"},
    5: {"tau": 40, "status": "Conjecture", "symmetry": "D5 Lattice"},
    8: {"tau": 240, "status": "Proven", "symmetry": "E8 Lattice"}
}

def generate_known_config(d):
    """Generate known optimal configuration (normalized)."""
    if d == 4:
        # 24-Cell
        pts = []
        # Type 1: Permutations of (±1, 0, 0, 0)
        for i in range(4):
            for s in [-1, 1]:
                v = np.zeros(4); v[i] = s
                pts.append(v)
        # Type 2: (±0.5, ±0.5, ±0.5, ±0.5)
        for s in product([-0.5, 0.5], repeat=4):
            pts.append(np.array(s))
        pts = np.array(pts)
        return pts / np.linalg.norm(pts, axis=1, keepdims=True)
        
    elif d == 5:
        # D5 (obtained from helper)
        pts = d5_shell_points(R=1.0)
        return pts / np.linalg.norm(pts, axis=1, keepdims=True)
        
    elif d == 8:
        # E8
        pts = []
        # Type 1: Permutations of (±1, ±1, 0...0)
        for idxs in combinations(range(8), 2):
            for s1 in [-1, 1]:
                for s2 in [-1, 1]:
                    v = np.zeros(8)
                    v[idxs[0]], v[idxs[1]] = s1, s2
                    pts.append(v)
        # Type 2: (±0.5)^8 with even sum of signs
        for s in product([-0.5, 0.5], repeat=8):
             if np.sum(np.array(s) < 0) % 2 == 0:
                 pts.append(np.array(s))
        pts = np.array(pts)
        return pts / np.linalg.norm(pts, axis=1, keepdims=True)

    return None

# -----------------------------------------------------
# 2. Hybrid Seeding
# -----------------------------------------------------

def random_rotation_matrix(d, rng):
    """Generate a random orthogonal matrix (Haar measure)."""
    H = rng.normal(size=(d, d))
    Q, R = np.linalg.qr(H)
    return Q

def generate_hybrid_seed(d, N, mode, R, rng):
    """
    Generate seed based on mode.
    Modes:
      0: "Random" (Pure random shell)
      1: "Rotated" (Randomly rotated known config + random fill if needed)
      2: "Partial" (Subset of known + random fill)
    """
    radius = 2.0 * R
    
    if mode == "Random":
        x = rng.normal(size=(N, d))
        return project_all(x, radius)
        
    known = generate_known_config(d)
    if known is None:
        raise ValueError(f"No known config for d={d}")
        
    # Scale known to correct radius
    known = project_all(known, radius)
        
    if mode == "Rotated":
        # Apply random rotation to full known config
        rot = random_rotation_matrix(d, rng)
        rotated_known = known @ rot.T
        
        if N == len(known):
            # Exact match - add certify-level noise (but harder: 0.2)
            noise = rng.normal(scale=0.2, size=rotated_known.shape)
            return project_all(rotated_known + noise, radius)
        elif N > len(known):
            # Rotated + Fill
            n_needed = N - len(known)
            fill = rng.normal(size=(n_needed, d))
            fill = project_all(fill, radius)
            combined = np.vstack([rotated_known, fill])
            # Add noise to everything
            noise = rng.normal(scale=0.2, size=combined.shape)
            return project_all(combined + noise, radius)
        else: # N < len(known)
            # Subset
            idxs = rng.choice(len(known), size=N, replace=False)
            subset = rotated_known[idxs]
            noise = rng.normal(scale=0.2, size=subset.shape)
            return project_all(subset + noise, radius)
        
    elif mode == "Partial":
        # Heuristic: 50% structural
        n_fixed = N // 2
        
        # Pick random subset of known points
        rot = random_rotation_matrix(d, rng)
        rotated_known = known @ rot.T
        
        # Guard if known is smaller than n_fixed (unlikely)
        n_avail = min(len(known), n_fixed)
        indices = rng.choice(len(known), size=n_avail, replace=False)
        fixed_part = rotated_known[indices]
        
        # Random fill
        n_random = N - n_avail
        random_part = rng.normal(size=(n_random, d))
        random_part = project_all(random_part, radius)
        
        combined = np.vstack([fixed_part, random_part])
        # Add small noise to whole thing
        return project_all(combined + rng.normal(scale=0.05, size=combined.shape), radius)
        
    else:
        raise ValueError(f"Unknown mode {mode}")

# -----------------------------------------------------
# 3. Annealed Optimizer
# -----------------------------------------------------

def run_annealed_repair(x0, R, params: OptParams, eps_g, eps_r):
    """
    Modified repair_then_polish with annealing in the repair phase.
    Relaxed -> Sharp constraints.
    """
    radius = 2.0 * R
    x = project_all(x0.copy(), radius)
    N, d = x.shape
    adam = AdamState((N, d))
    
    # Annealing schedule for tau (smoothness of penalty)
    # Start huge (soft) -> End small (sharp)
    tau_start = 0.5
    tau_end = 0.05
    
    # Track BEST gap seen at any point (not just final)
    best_min_gap = -np.inf 
    
    # -- REPAIR (Annealed) --
    for it in range(params.repair_iters):
        # Linear annealing of tau
        # Fix: max(..., 1) to avoid division by zero or index issues
        # progress goes 0.0 -> 1.0 exactly
        progress = it / max(params.repair_iters - 1, 1)
        current_tau = tau_start + (tau_end - tau_start) * progress
        
        g = min_gap(x, R)
        if g > best_min_gap:
            best_min_gap = g
            
        # Early exit if good enough to polish
        if g > params.repair_target:
            break
            
        _, grad = overlap_penalty_and_grad(x, R, current_tau)
        grad_tan = project_grad_tangent(x, grad)
        
        # Clip
        grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
        grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
        
        step = adam.step(grad_tan, params.repair_eta)
        x = x - step
        x = project_all(x, radius)
        
    # -- POLISH (Standard) --
    adam = AdamState((N, d))
    tau = params.polish_tau0
    
    for it in range(params.polish_iters):
        g = min_gap(x, R)
        re = radial_error(x, R)
        
        if g > best_min_gap:
            best_min_gap = g
            
        if (g >= -eps_g) and (re <= eps_r):
            # Certified!
            return True, g, x, best_min_gap
            
        _, grad = logsumexp_maxmin_and_grad(x, R, tau)
        grad_tan = project_grad_tangent(x, grad)
        
        grad_norms = np.linalg.norm(grad_tan, axis=1, keepdims=True) + 1e-12
        grad_tan = grad_tan * np.minimum(1.0, params.max_step_norm / grad_norms)
        
        step = adam.step(grad_tan, params.polish_eta)
        x = x - step
        x = project_all(x, radius)
        
        tau = max(params.polish_tau_min, tau * params.polish_tau_decay)
        
    return False, min_gap(x, R), x, best_min_gap

# -----------------------------------------------------
# 4. Fingerprint & Verdict
# -----------------------------------------------------

def compute_fingerprint_score(points, known_points):
    """
    Compare fingerprint of points vs known_points.
    Score = Fraction of inner products that match the known distribution 
    within tolerance.
    """
    # Self-dots
    dots_test = (points @ points.T)[np.triu_indices(len(points), k=1)]
    dots_known = (known_points @ known_points.T)[np.triu_indices(len(known_points), k=1)]
    
    bins = np.linspace(-1, 1, 50)
    hist_test, _ = np.histogram(dots_test, bins=bins, density=True)
    hist_known, _ = np.histogram(dots_known, bins=bins, density=True)
    
    # L1 distance between histograms (0 = perfect match, 2 = discrete disjoint)
    diff = np.sum(np.abs(hist_test - hist_known)) * (bins[1] - bins[0])
    return 1.0 - (diff / 2.0) # Similarity approx [0, 1]

# -----------------------------------------------------
# 5. Main Harness
# -----------------------------------------------------

def run_basin_widening():
    print("=== Sprint 5.17: Basin Widening & Hybrid Seeding (v2) ===")
    
    dims = [4, 5]
    modes = ["Random", "Partial", "Rotated"]
    budget = 20
    R = 1.0
    
    params = OptParams(
        repair_iters=10000, 
        polish_iters=15000,
        max_step_norm=0.02
    )
    
    rng = np.random.default_rng(517)
    
    final_output = {}
    
    for d in dims:
        tau = KISSING_NUMBERS[d]["tau"]
        sym = KISSING_NUMBERS[d]["symmetry"]
        known_pts_ref = generate_known_config(d)
        known_pts_ref = project_all(known_pts_ref, 2.0*R) # Scale for fingerprinting
        
        print(f"\n{'='*50}")
        print(f"Dimension {d} (Tau={tau}, {sym})")
        print(f"{'='*50}")
        
        # Test Tau and Tau+1
        for N in [tau, tau + 1]:
            print(f"\n--- Testing N={N} ---")
            
            for mode in modes:
                # If N=tau+1, Rotated/Partial still use the Tau-based structure + fill
                # This tests if structure hallucinates success
                
                print(f"  > Mode: {mode}")
                successes = 0
                near_misses = 0
                best_overall_gap = -np.inf
                best_fp_score = 0.0
                
                for r in range(budget):
                    x0 = generate_hybrid_seed(d, N, mode, R, rng)
                    
                    # Run Optimization
                    cert, finals_gap, final_x, best_run_gap = run_annealed_repair(
                        x0, R, params, 1e-6, 1e-6
                    )
                    
                    if best_run_gap > best_overall_gap:
                        best_overall_gap = best_run_gap
                        # Compute FP score for the best run
                        if N == tau: # Only meaningful to compare to known tau structure
                            fp_score = compute_fingerprint_score(final_x, known_pts_ref)
                            if fp_score > best_fp_score:
                                best_fp_score = fp_score
                    
                    if cert:
                        successes += 1
                        near_misses += 1 # Certified counts as near miss too
                    elif best_run_gap > -0.05:
                         # Check basin width/near miss
                         near_misses += 1
                        
                rate = (successes / budget) * 100
                miss_rate = (near_misses / budget) * 100
                
                print(f"    Certified: {successes}/{budget} ({rate:.1f}%)")
                print(f"    Basin Entry (> -0.05): {near_misses}/{budget} ({miss_rate:.1f}%)")
                print(f"    Best Gap: {best_overall_gap:.6f}")
                if N == tau:
                    print(f"    FP Similarity: {best_fp_score:.3f}")
                
                # Verdict logic (only printed for N=tau usually, but good to see for N+1)
                if rate > 20: 
                    verdict = "CALIBRATED"
                elif rate > 0:
                    verdict = "WEAKLY CALIBRATED"
                else:
                    verdict = "UNCALIBRATED"
                    
                print(f"    Verdict: [{verdict}]")
                
                final_output[f"d{d}_N{N}_{mode}"] = {
                    "success_rate": rate,
                    "basin_rate": miss_rate,
                    "best_gap": best_overall_gap,
                    "fp_score": best_fp_score if N==tau else 0.0
                }

    # Dump results
    print("\nSummary written to sprint517_results.json")
    with open("sprint517_results.json", "w") as f:
        json.dump(final_output, f, indent=2)

if __name__ == "__main__":
    run_basin_widening()
