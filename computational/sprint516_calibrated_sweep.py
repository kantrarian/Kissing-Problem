"""Sprint 5.16: Calibrated Universal Dimensionality Check"""
import numpy as np
import time
import json
from itertools import combinations, permutations, product
from scipy.spatial.distance import pdist, squareform
from sprint59c_control_first import repair_then_polish, OptParams, random_shell

# -----------------------------------------------------
# Knowledge Base: Proven/Conjectured Kissing Numbers
# -----------------------------------------------------
# Status: "Proven" (Exact), "Conjecture" (Bounds)
KISSING_NUMBERS = {
    2: {"tau": 6, "status": "Proven", "symmetry": "Hexagon"},
    3: {"tau": 12, "status": "Proven", "symmetry": "Icosahedron"},
    4: {"tau": 24, "status": "Proven", "symmetry": "24-Cell"},
    5: {"tau": 40, "status": "Conjecture (40-44)", "symmetry": "D5 Lattice"},
    6: {"tau": 72, "status": "Conjecture (72-78)", "symmetry": "E6 Lattice"},
    7: {"tau": 126, "status": "Conjecture (126-134)", "symmetry": "E7 Lattice"},
    8: {"tau": 240, "status": "Proven", "symmetry": "E8 Lattice"},
    24: {"tau": 196560, "status": "Proven", "symmetry": "Leech Lattice"}
}

# -----------------------------------------------------
# 1. Structured Seed Generation
# -----------------------------------------------------

def generate_known_config(d, noise_scale=0.0):
    """
    Generate the known optimal configuration for dimension d.
    Returns (points, symmetry_name).
    """
    if d == 2:
        # Hexagon
        angles = np.linspace(0, 2*np.pi, 6, endpoint=False)
        pts = np.column_stack([np.cos(angles), np.sin(angles)])
        return pts, "Hexagon"
        
    elif d == 3:
        # Icosahedron (12 vertices)
        phi = (1 + np.sqrt(5)) / 2
        verts = []
        # (0, ±1, ±phi) cyclic perms
        for i in [-1, 1]:
            for j in [-phi, phi]:
                verts.append([0, i, j])
                verts.append([j, 0, i])
                verts.append([i, j, 0])
        pts = np.array(verts)
        return pts / np.linalg.norm(pts[0]), "Icosahedron"
        
    elif d == 4:
        # 24-Cell: Permutations of (±1, ±1, 0, 0) and (±0.5, ±0.5, ±0.5, ±0.5)??
        # Usually defined as: 24 vertices 
        # 1) 16 vertices of form (±0.5, ±0.5, ±0.5, ±0.5)
        # 2) 8 vertices of form permutations of (±1, 0, 0, 0)
        # Let's normalize everything to unit sphere.
        # Let's normalize everything to unit sphere.
        pts = []
        # Type 1: Permutations of (+-1, 0, 0, 0) -> 8 points
        for i in range(4):
            for s in [-1, 1]:
                v = np.zeros(4); v[i] = s
                pts.append(v)
        # Type 2: (±0.5, ±0.5, ±0.5, ±0.5) -> 16 points
        for s in product([-0.5, 0.5], repeat=4):
            pts.append(np.array(s))
        pts = np.array(pts)
        pts = pts / np.linalg.norm(pts, axis=1, keepdims=True)
        return pts, "24-Cell"
        
    elif d == 5:
        # D5 (40 vertices)
        # Permutations of (±1, ±1, 0, 0, 0) / sqrt(2)
        # Permutations of (±1, ±1, 0, 0, 0) / sqrt(2)
        base = [1, 1, 0, 0, 0]
        uniq_perms = set(permutations(base))
        pts = []
        for p in uniq_perms:
            idxs = [i for i, x in enumerate(p) if x != 0]
            for signs in product([-1, 1], repeat=2):
                v = list(p)
                v[idxs[0]] *= signs[0]
                v[idxs[1]] *= signs[1]
                pts.append(v)
        pts = np.array(list(set(tuple(x) for x in pts))) # Dedup
        pts = pts / np.linalg.norm(pts, axis=1, keepdims=True)
        return pts, "D5 Lattice"
        
    elif d == 8:
        # E8 (240 vertices)
        # 1) All perms of (±1, ±1, 0x6) -> 4*C(8,2) = 4*28 = 112
        # 2) (±0.5)^8 with even number of minus signs -> 2^7 = 128
        # Total = 240
        # Root system is usually scaled to norm sqrt(2). Normalize to 1.
        pts = []
        # Type 1
        # Type 1
        base = [1, 1] + [0]*6
        # This is slow if naive. Optimized generation:
        for idxs in combinations(range(8), 2):
            for s1 in [-1, 1]:
                for s2 in [-1, 1]:
                    v = np.zeros(8)
                    v[idxs[0]] = s1
                    v[idxs[1]] = s2
                    pts.append(v)
        # Type 2
        for s in product([-0.5, 0.5], repeat=8):
             if np.sum(np.array(s) < 0) % 2 == 0:
                 pts.append(np.array(s))
        pts = np.array(pts)
        pts = pts / np.linalg.norm(pts, axis=1, keepdims=True)
        return pts, "E8 Lattice"

    else:
        return None, "Unknown"

def add_noise(points, scale=0.01, rng=None):
    if rng is None: rng = np.random.default_rng()
    noise = rng.normal(scale=scale, size=points.shape)
    p_noisy = points + noise
    return p_noisy / np.linalg.norm(p_noisy, axis=1, keepdims=True)


# -----------------------------------------------------
# 2. Fingerprinting
# -----------------------------------------------------
def compute_fingerprint(points, tol=1e-4):
    """
    Compute distribution of inner products (rounded).
    Returns list of (value, count).
    """
    dots = points @ points.T
    # Extract upper triangle off-diagonal
    N = points.shape[0]
    triu = np.triu_indices(N, k=1)
    vals = dots[triu]
    
    # Round and count
    rounded = np.round(vals / tol) * tol
    unique, counts = np.unique(rounded, return_counts=True)
    
    # Sort by value
    spectrum = sorted(zip(unique, counts), key=lambda x: x[0])
    
    # Also return eigenvalues of Gram matrix
    evals = np.linalg.eigvalsh(dots)
    
    return {
        "spectrum": [(float(v), int(c)) for v, c in spectrum if c > 0],
        "min_eval": float(np.min(evals)),
        "max_eval": float(np.max(evals))
    }


# -----------------------------------------------------
# 3. Calibrated Run Harness
# -----------------------------------------------------

def run_calibrated_sprint():
    print(f"{'='*60}")
    print(f"Sprint 5.16: Calibrated Universal Dimensionality Check")
    print(f"{'='*60}")
    
    dims_to_test = [2, 3, 4, 5, 8] # 8 is bold but good for "Proven" tier
    
    # Baseline Parameters
    base_params = OptParams(
        repair_iters=20000,
        polish_iters=30000,
        polish_tau_min=1e-8
    )
    
    rng = np.random.default_rng(42)
    R = 1.0
    
    results_matrix = {}
    
    for d in dims_to_test:
        info = KISSING_NUMBERS.get(d, {})
        tau = info.get("tau", "?")
        status = info.get("status", "Unknown")
        sym = info.get("symmetry", "None")
        
        print(f"\n[{status}] Dim {d}: Tau={tau} ({sym})")
        
        # --- PHASE A: Calibration (Certify Mode) ---
        # Can we recover the known config from Seed + Noise?
        pts_known, name = generate_known_config(d)
        
        if pts_known is not None:
             # Add tiny noise to simulate "near miss"
             x0 = add_noise(pts_known, scale=0.1, rng=rng)
             print(f"  [Certify Mode] Starting from noisy {name} (scale=0.1)...")
             
             res = repair_then_polish(x0, R, base_params, eps_g=1e-8, eps_r=1e-8)
             gap = res["final_min_gap"]
             is_cert = (gap > -1e-6)
             
             print(f"    -> Re-discovered gap: {gap:.9f} {'[CERTIFIED]' if is_cert else '[FAIL]'}")
             
             if is_cert:
                 fp = compute_fingerprint(res["final_points"])
                 print(f"    -> Spectrum: {[f'{v:.2f} ({c})' for v,c in fp['spectrum'] if v > -0.9]}")
        else:
            print("  [Certify Mode] No known config generator.")
            
        # --- PHASE B: Budget Tuning (Discover Mode) ---
        # How many restarts needed to find Tau from random?
        # Start small, scale up if needed.
        # But for d=8 (E8), random search often fails. We should know this.
        
        restarts_budget = 10
        if d >= 6: restarts_budget = 20 # Give more time for high dims
        
        print(f"  [Discover Mode] Running {restarts_budget} random restarts for N={tau}...")
        
        success_count = 0
        best_gap = -np.inf
        
        t0 = time.time()
        for r in range(restarts_budget):
            seed_rng = np.random.default_rng(r + 100*d) # Distinct seeds
            x0 = random_shell(tau, d, R, seed_rng)
            res = repair_then_polish(x0, R, base_params, eps_g=1e-8, eps_r=1e-8)
            g = res["final_min_gap"]
            
            if g > best_gap: best_gap = g
            if g > -1e-6: success_count += 1
            
        duration = time.time() - t0
        success_rate = (success_count / restarts_budget) * 100
        print(f"    -> Success Rate: {success_count}/{restarts_budget} ({success_rate:.1f}%)")
        print(f"    -> Best Gap: {best_gap:.9f}")
        
        # Verdict logic
        calibrated = False
        if success_rate > 20: # If we can find it >20% of time, random search is viable
            calibrated = True
            print("    -> CALIBRATED: Random search is viable.")
        else:
            print("    -> UNCALIBRATED: Random search struggles. 'Failure' on N+1 is weak evidence here.")
            
        # --- PHASE C: Falsification (N+1) ---
        # Run N+1 ONLY if calibrated or if d=5 (the test case)
        if calibrated or d == 5:
            n_fail = tau + 1
            print(f"  [Falsification] Running {restarts_budget} random restarts for N={n_fail}...")
            
            best_gap_fail = -np.inf
            
            for r in range(restarts_budget):
                seed_rng = np.random.default_rng(r + 200*d)
                x0 = random_shell(n_fail, d, R, seed_rng)
                res = repair_then_polish(x0, R, base_params, eps_g=1e-8, eps_r=1e-8)
                g = res["final_min_gap"]
                if g > best_gap_fail: best_gap_fail = g
                
            print(f"    -> Best Gap (N={n_fail}): {best_gap_fail:.9f}")
            
            # Final Contrast
            gap_delta = best_gap - best_gap_fail
            print(f"  [Contrast] Gap Delta = {gap_delta:.9f}")
            if gap_delta > 0.01:
                print("    -> STRONG EVIDENCE: Clear separation.")
            else:
                print("    -> WEAK EVIDENCE: Separation unclear.")


if __name__ == "__main__":
    run_calibrated_sprint()
