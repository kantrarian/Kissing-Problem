"""
Sprint 5.7: Diagnostic Re-run (ENHANCED VERSION)
=================================================
Diagnostic-enhanced certification for 5D kissing number investigation.

Key enhancements over Sprint 5.6:
1. Preserves insertion_details in JSON output
2. Tracks best_approach diagnostics (min_gap, max_rad_err, gap_violations)
3. Records failure_stage (no_path, approach_only, cert_retry_fail)
4. Adds achieved_loose check with eps_g = 1e-3
5. Captures certification retry diagnostics
6. Tracks best_postcert_min_gap

Purpose: Distinguish "hard wall" (geometric obstruction) vs "polishing failure"
(certifier too strict). This enables scientific interpretation of 0% certification rates.

Known bounds: 40 <= tau_5 <= 44
- D_5 root system gives 40 kissing spheres
- Upper bound 44 from Levenshtein (1979)

Expected runtime: 5-10 minutes for diagnostic run (N=41, N=42, 10 seeds)
"""

import numpy as np
import matplotlib.pyplot as plt
import json
import time
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# =============================================================================
# CONFIGURATION
# =============================================================================
CONFIG = {
    # Search parameters
    "n_seeds": 10,              # Seeds per N value
    "K_seams": 50,              # Seam directions per insertion attempt
    "K_seams_hard": 100,        # Extra seams for difficult cases (N>=44)
    
    # Certification tolerances (STRICT)
    "cert_eps_r": 1e-5,         # Radial tolerance: |||x|| - 2R| <= eps_r
    "cert_eps_g": 1e-5,         # Gap tolerance: min_gap >= -eps_g
    "cert_max_iters": 1000,     # Max certification iterations
    
    # Approach parameters
    "n_approach_steps": 60,     # Steps in radial approach
    "n_relax_steps": 15,        # Shell relaxation steps per approach step
    "approach_eta": 0.012,      # Learning rate for approach
    "cert_eta": 0.003,          # Learning rate for certification relaxation
    
    # Physics
    "omega": 25.0,              # Repulsion strength
    "beta": 50.0,               # Softmin temperature
    
    # Geometry
    "shell_jitter": 0.02,       # Initial shell jitter
    "dir_jitter": 0.03,         # Direction jitter
    
    # Test cases
    "N_values": [41, 42, 43, 44, 45],  # N=45 is falsification test
    
    # Diagnostic parameters
    "loose_eps_g": 1e-3,         # Loose threshold for achieved_loose check
    "n_seeds_diagnostic": 10,    # Reduced seeds for diagnostic run
    
    # Output
    "save_configs": True,       # Save certified configurations
    "output_dir": "./sprint57_results",
}

# =============================================================================
# CORE GEOMETRY
# =============================================================================
def project_to_sphere(x, radius):
    """Project point to sphere surface."""
    n = np.linalg.norm(x)
    if n < 1e-14:
        y = np.zeros_like(x)
        y[0] = radius
        return y
    return radius * x / n

def tangential_component(x, grad):
    """Extract tangential component of gradient (perpendicular to radial)."""
    xhat = x / (np.linalg.norm(x) + 1e-14)
    return grad - np.dot(grad, xhat) * xhat

def d_root_points(d):
    """
    D_d root system: 2*d*(d-1) points on unit sphere.
    For d=5: 40 points (the known lower bound for tau_5).
    """
    pts = []
    for i in range(d):
        for j in range(i+1, d):
            for si in (-1.0, 1.0):
                for sj in (-1.0, 1.0):
                    v = np.zeros(d)
                    v[i] = si
                    v[j] = sj
                    pts.append(v / np.linalg.norm(v))
    return np.asarray(pts)

def random_spherical_points(d, n, rng):
    """Generate n random points uniformly on S^(d-1)."""
    pts = rng.normal(size=(n, d))
    return np.array([p / np.linalg.norm(p) for p in pts])

def jitter_shell(shell_pts, sigma, rng, radius):
    """Add jitter to shell and reproject to sphere."""
    jittered = shell_pts + sigma * rng.normal(size=shell_pts.shape)
    return np.array([project_to_sphere(p, radius) for p in jittered])

def jitter_direction(u, sigma, rng):
    """Add jitter to direction and renormalize."""
    v = u + sigma * rng.normal(size=u.shape)
    return v / (np.linalg.norm(v) + 1e-14)

# =============================================================================
# SEAM DIRECTION GENERATION
# =============================================================================
def closest_pair_seam_dirs(shell_pts_unit, K=50):
    """
    Structured seam directions: midpoints of closest pairs.
    These target the natural "gaps" in the shell.
    """
    n = len(shell_pts_unit)
    pairs = []
    for i in range(n):
        for j in range(i+1, n):
            d = np.linalg.norm(shell_pts_unit[i] - shell_pts_unit[j])
            pairs.append((d, i, j))
    pairs.sort(key=lambda t: t[0])
    
    dirs = []
    seen = set()
    for _, i, j in pairs[:K*3]:  # Oversample to handle duplicates
        u = shell_pts_unit[i] + shell_pts_unit[j]
        norm = np.linalg.norm(u)
        if norm < 1e-10:
            continue
        u = u / norm
        # Deduplicate
        u_key = tuple(np.round(u, 5))
        if u_key not in seen:
            seen.add(u_key)
            dirs.append(u)
        if len(dirs) >= K:
            break
    return dirs[:K]

def random_sphere_dirs(d, K, rng):
    """Random directions uniformly on S^(d-1)."""
    dirs = []
    for _ in range(K):
        v = rng.normal(size=d)
        dirs.append(v / (np.linalg.norm(v) + 1e-14))
    return dirs

def antipodal_seam_dirs(shell_pts_unit, K=20):
    """
    Antipodal directions: regions furthest from all shell points.
    These target the "empty" regions.
    """
    d = shell_pts_unit.shape[1]
    
    # Sample many random directions and keep those far from shell
    n_samples = K * 20
    rng = np.random.default_rng(12345)
    candidates = random_sphere_dirs(d, n_samples, rng)
    
    # Score by minimum distance to any shell point
    scores = []
    for u in candidates:
        min_dist = min(np.linalg.norm(u - s) for s in shell_pts_unit)
        scores.append((min_dist, u))
    
    scores.sort(key=lambda x: -x[0])  # Descending by distance
    return [s[1] for s in scores[:K]]

def combined_seam_dirs(shell_pts_unit, K, rng):
    """
    Combined strategy: structured + random + antipodal.
    Ensures comprehensive coverage of direction space.
    """
    K_struct = K // 3
    K_anti = K // 3
    K_rand = K - K_struct - K_anti
    
    struct_dirs = closest_pair_seam_dirs(shell_pts_unit, K_struct)
    anti_dirs = antipodal_seam_dirs(shell_pts_unit, K_anti)
    rand_dirs = random_sphere_dirs(shell_pts_unit.shape[1], K_rand, rng)
    
    return struct_dirs + anti_dirs + rand_dirs

# =============================================================================
# CERTIFICATION (CRITICAL)
# =============================================================================
def check_configuration(all_points, R=1.0, eps_r=1e-5, eps_g=1e-5):
    """
    Check if configuration satisfies kissing constraints.
    
    Constraints:
    1. All points on sphere of radius 2R: |||x_i|| - 2R| <= eps_r
    2. No overlaps: min_{i<j} (||x_i - x_j|| - 2R) >= -eps_g
    
    Returns:
        is_valid: bool
        max_radial_error: float
        min_gap: float
        diagnostics: dict
    """
    radius = 2.0 * R
    n = len(all_points)
    
    # Radial constraint
    radii = np.array([np.linalg.norm(p) for p in all_points])
    radial_errors = np.abs(radii - radius)
    max_radial_error = np.max(radial_errors)
    mean_radial_error = np.mean(radial_errors)
    
    # Pairwise gap constraint
    min_gap = np.inf
    gap_violations = 0
    total_pairs = 0
    
    for i in range(n):
        for j in range(i+1, n):
            dist = np.linalg.norm(all_points[i] - all_points[j])
            gap = dist - 2.0 * R
            min_gap = min(min_gap, gap)
            total_pairs += 1
            if gap < -eps_g:
                gap_violations += 1
    
    # Valid only if BOTH constraints satisfied
    radial_ok = max_radial_error <= eps_r
    gap_ok = min_gap >= -eps_g
    is_valid = radial_ok and gap_ok
    
    diagnostics = {
        "n_points": n,
        "max_radial_error": max_radial_error,
        "mean_radial_error": mean_radial_error,
        "min_gap": min_gap,
        "gap_violations": gap_violations,
        "total_pairs": total_pairs,
        "radial_ok": radial_ok,
        "gap_ok": gap_ok,
        "eps_r": eps_r,
        "eps_g": eps_g
    }
    
    return is_valid, max_radial_error, min_gap, diagnostics

def certify_configuration(all_points, R=1.0, eps_r=1e-5, eps_g=1e-5,
                          max_iters=1000, eta=0.003, omega=30.0,
                          verbose=False):
    """
    Attempt to certify configuration by projecting to valid kissing arrangement.
    
    Algorithm:
    1. Project all points to sphere (enforce radial constraint exactly)
    2. Iterative repulsion to resolve overlaps (with tangential moves only)
    3. Verify final configuration meets tolerances
    
    Returns:
        certified: bool
        final_points: array
        diagnostics: dict
    """
    radius = 2.0 * R
    n = len(all_points)
    
    # Step 1: Project to sphere (radial constraint now satisfied exactly)
    points = np.array([project_to_sphere(p, radius) for p in all_points])
    
    # Track convergence
    gap_history = []
    
    # Step 2: Repulsion relaxation
    for iteration in range(max_iters):
        # Check current state
        is_valid, rad_err, min_gap, diag = check_configuration(
            points, R, eps_r, eps_g
        )
        gap_history.append(min_gap)
        
        if is_valid:
            return True, points, {
                "iterations": iteration,
                "converged": True,
                "final_min_gap": min_gap,
                "final_radial_error": rad_err,
                "gap_history": gap_history[-100:]  # Last 100 for diagnostics
            }
        
        # If severely overlapped and not improving, abort
        if min_gap < -0.5:
            return False, points, {
                "iterations": iteration,
                "converged": False,
                "reason": "severe_overlap",
                "min_gap": min_gap
            }
        
        # Check for stagnation (no improvement in last 50 iters)
        if iteration > 100 and len(gap_history) > 50:
            recent_improvement = gap_history[-50] - gap_history[-1]
            if abs(recent_improvement) < 1e-8:
                # Stagnated - final check
                if is_valid:
                    return True, points, {
                        "iterations": iteration,
                        "converged": True,
                        "reason": "stagnated_valid",
                        "final_min_gap": min_gap
                    }
                else:
                    return False, points, {
                        "iterations": iteration,
                        "converged": False,
                        "reason": "stagnated_invalid",
                        "final_min_gap": min_gap
                    }
        
        # Compute repulsion gradients
        grads = np.zeros_like(points)
        
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                dvec = points[i] - points[j]
                dist = np.linalg.norm(dvec) + 1e-14
                gap = dist - 2.0 * R
                
                # Repulsion: exponential, stronger when overlapping
                if gap < 0.2:  # Only repel when close
                    # Exponential repulsion
                    force_mag = omega * np.exp(-2.0 * gap)
                    grads[i] += (force_mag / dist) * dvec
        
        # Update with tangential projection (stay exactly on sphere)
        for i in range(n):
            g_tan = tangential_component(points[i], grads[i])
            new_pos = points[i] + eta * g_tan
            points[i] = project_to_sphere(new_pos, radius)
    
    # Max iterations reached
    is_valid, rad_err, min_gap, _ = check_configuration(points, R, eps_r, eps_g)
    
    return is_valid, points, {
        "iterations": max_iters,
        "converged": is_valid,
        "reason": "max_iters",
        "final_min_gap": min_gap,
        "final_radial_error": rad_err
    }

# =============================================================================
# SHELL DYNAMICS
# =============================================================================
def relax_shell_on_sphere(shell_pos, intruder_pos, R=1.0, omega=25.0,
                          n_steps=15, eta=0.012):
    """
    Relax shell in response to intruder using gradient descent on sphere.
    """
    radius = 2.0 * R
    shell = np.array([project_to_sphere(p, radius) for p in shell_pos])
    
    for _ in range(n_steps):
        grads = np.zeros_like(shell)
        
        for i in range(len(shell)):
            xi = shell[i]
            
            # Shell-shell repulsion
            for j in range(len(shell)):
                if i == j:
                    continue
                xj = shell[j]
                dvec = xi - xj
                dist = np.linalg.norm(dvec) + 1e-14
                gap = dist - 2.0 * R
                force = omega * np.exp(-gap)
                grads[i] += (force / dist) * dvec
            
            # Shell-intruder repulsion
            dvec = xi - intruder_pos
            dist = np.linalg.norm(dvec) + 1e-14
            gap = dist - 2.0 * R
            force = omega * np.exp(-gap)
            grads[i] += (force / dist) * dvec
        
        # Tangential update
        for i in range(len(shell)):
            g_tan = tangential_component(shell[i], grads[i])
            shell[i] = project_to_sphere(shell[i] + eta * g_tan, radius)
    
    return shell

def compute_xi0(all_points, prev_points, R=1.0, omega=25.0, beta=50.0):
    """
    Compute Xi0 (dynamics signal) from configuration change.
    
    Xi0 = ‖[G, Ġ]‖_F / (‖G‖_F · ‖Ġ‖_F)
    
    Where G is the generator matrix and Ġ is its time derivative.
    """
    def softmin(values, beta=50.0):
        v = np.asarray(values, dtype=float)
        shift = np.min(v)
        return shift - (1.0 / beta) * np.log(np.sum(np.exp(-beta * (v - shift))))
    
    def compute_G(positions):
        N = len(positions)
        G = np.zeros((N, N))
        for i in range(N):
            gaps = []
            for j in range(N):
                if i == j:
                    continue
                dist = np.linalg.norm(positions[i] - positions[j])
                gap = dist - 2.0 * R
                gaps.append(gap)
                G[i, j] = omega * np.exp(-gap)
            G[i, i] = omega * softmin(gaps, beta=beta)
        return G
    
    G_curr = compute_G(all_points)
    G_prev = compute_G(prev_points)
    G_dot = G_curr - G_prev
    
    # Commutator
    comm = G_curr @ G_dot - G_dot @ G_curr
    
    # Normalized commutator norm
    lam = np.linalg.norm(comm, ord='fro')
    norm_factor = np.linalg.norm(G_curr, 'fro') * np.linalg.norm(G_dot, 'fro') + 1e-14
    
    xi0 = lam / norm_factor
    
    # Also compute delta_min (spectral gap)
    evals = np.linalg.eigvalsh(G_curr)
    gaps = np.diff(np.sort(evals))
    delta_min = np.min(np.abs(gaps)) if len(gaps) > 0 else 1e-14
    
    return xi0, delta_min

# =============================================================================
# INSERTION WITH CERTIFICATION
# =============================================================================
def attempt_insertion_certified(
    shell_pts, intruder_dir, R=1.0,
    n_approach=60, n_relax=15, eta_approach=0.012,
    cert_eps_r=1e-5, cert_eps_g=1e-5, cert_iters=1000, cert_eta=0.003,
    omega=25.0, track_xi0=True
):
    """
    Attempt to insert intruder sphere and CERTIFY the result.
    
    Two-phase approach:
    1. Approach: bring intruder in while relaxing shell
    2. Certify: project to valid configuration with tight tolerances
    
    Returns:
        certified: bool (TRUE only if passes STRICT certification)
        final_config: array (N+1 points) or None
        diagnostics: dict with full trajectory info
    """
    radius = 2.0 * R
    shell = np.array([project_to_sphere(p, radius) for p in shell_pts])
    n_shell = len(shell)
    
    # Track trajectory
    trajectory = {
        "r_values": [],
        "min_gaps": [],
        "xi0_values": [] if track_xi0 else None,
        "delta_min_values": [] if track_xi0 else None
    }
    
    best_config = None
    best_min_gap = -np.inf
    prev_all_points = None
    
    # Approach phase
    r_vals = np.linspace(3.5, 2.005, n_approach)
    
    for r in r_vals:
        intruder = r * intruder_dir
        shell = relax_shell_on_sphere(
            shell, intruder, R=R, omega=omega,
            n_steps=n_relax, eta=eta_approach
        )
        
        # Current configuration
        intruder_on_sphere = project_to_sphere(intruder, radius)
        all_points = np.vstack([shell, intruder_on_sphere])
        
        # Check gaps
        _, _, min_gap, _ = check_configuration(all_points, R, eps_r=0.1, eps_g=0.1)
        
        trajectory["r_values"].append(r)
        trajectory["min_gaps"].append(min_gap)
        
        # Track Xi0 if requested
        if track_xi0 and prev_all_points is not None:
            xi0, delta_min = compute_xi0(all_points, prev_all_points, R=R, omega=omega)
            trajectory["xi0_values"].append(xi0)
            trajectory["delta_min_values"].append(delta_min)
        elif track_xi0:
            trajectory["xi0_values"].append(np.nan)
            trajectory["delta_min_values"].append(np.nan)
        
        prev_all_points = all_points.copy()
        
        # Track best configuration encountered
        if min_gap > best_min_gap:
            best_min_gap = min_gap
            best_config = all_points.copy()
        
        # Stop if deep overlap (unsalvageable)
        if min_gap < -0.4:
            break
    
    # Approach result
    approach_best_gap = best_min_gap
    approach_success = (best_min_gap > -0.2)
    
    if best_config is None:
        return False, None, {
            "approach_success": False,
            "reason": "no_config",
            "trajectory": trajectory
        }
    
    # CERTIFICATION PHASE
    certified, final_config, cert_diag = certify_configuration(
        best_config, R=R,
        eps_r=cert_eps_r, eps_g=cert_eps_g,
        max_iters=cert_iters, eta=cert_eta, omega=omega*1.5
    )
    
    # Final Xi0 if certified
    final_xi0 = None
    final_delta_min = None
    if certified and track_xi0:
        # Compute Xi0 at certified configuration vs pre-certification
        final_xi0, final_delta_min = compute_xi0(final_config, best_config, R=R, omega=omega)
    
    return certified, final_config, {
        "approach_success": approach_success,
        "approach_best_gap": approach_best_gap,
        "certified": certified,
        "certification": cert_diag,
        "trajectory": trajectory,
        "final_xi0": final_xi0,
        "final_delta_min": final_delta_min
    }

# =============================================================================
# MAIN PROBE FUNCTIONS
# =============================================================================
def probe_single_N(
    N_target, 
    n_seeds=50,
    K_seams=50,
    config=None,
    seed=42,
    verbose=True
):
    """
    Probe whether N_target spheres can achieve certified kissing configuration.
    
    Starts from D₅ (40 spheres) and attempts sequential insertion to N_target.
    """
    if config is None:
        config = CONFIG
    
    rng = np.random.default_rng(seed)
    R = 1.0
    radius = 2.0 * R
    
    d5_roots = d_root_points(5)
    base_N = len(d5_roots)  # 40
    
    cert_eps_r = config["cert_eps_r"]
    cert_eps_g = config["cert_eps_g"]
    cert_iters = config["cert_max_iters"]
    
    results = []
    certified_configs = []
    
    if verbose:
        print(f"\nProbing N = {N_target} with {n_seeds} seeds...")
    
    for s in range(n_seeds):
        if verbose and (s + 1) % 10 == 0:
            print(f"  Seed {s+1}/{n_seeds}...")
        
        # Start from jittered D₅
        shell = jitter_shell(d5_roots.copy(), config["shell_jitter"], rng, radius)
        current_N = base_N
        
        seed_result = {
            "seed": s,
            "target_N": N_target,
            "achieved_N": base_N,
            "certified": False,
            "insertion_details": [],
            # NEW DIAGNOSTIC FIELDS:
            "best_approach_min_gap": None,  # Best across all insertion attempts
            "best_approach_max_rad_err": None,
            "best_approach_gap_violations": None,
            "best_postcert_min_gap": None,  # Best after certification retry
            "failure_stage": None,  # Final failure stage
            "achieved_loose": False  # Whether achieved with eps_g = 1e-3
        }
        
        # Sequential insertion
        while current_N < N_target:
            # Use more seams for harder cases
            K = K_seams if current_N < 43 else config.get("K_seams_hard", K_seams * 2)
            
            seam_dirs = combined_seam_dirs(shell / radius, K, rng)
            
            seam_dirs = combined_seam_dirs(shell / radius, K, rng)
            
            # NEW: direction/attempt counters (per insertion step)
            n_dirs_generated = len(seam_dirs)
            n_dirs_evaluated = 0
            n_approaches_successful = 0
            first_failure_reason = None
            
            # Track best attempts
            best_certified_config = None
            best_certified_gap = -np.inf
            best_approach_config = None
            best_approach_gap = -np.inf
            best_approach_diag = None
            
            for u in seam_dirs:
                n_dirs_evaluated += 1
                u_jit = jitter_direction(u, config["dir_jitter"], rng)
                
                certified, final_config, diag = attempt_insertion_certified(
                    shell, u_jit, R=R,
                    n_approach=config["n_approach_steps"],
                    n_relax=config["n_relax_steps"],
                    eta_approach=config["approach_eta"],
                    cert_eps_r=cert_eps_r,
                    cert_eps_g=cert_eps_g,
                    cert_iters=cert_iters,
                    cert_eta=config["cert_eta"],
                    omega=config["omega"],
                    track_xi0=True
                )
                
                if certified and final_config is not None:
                    _, _, min_gap, _ = check_configuration(final_config, R, cert_eps_r, cert_eps_g)
                    if min_gap > best_certified_gap:
                        best_certified_gap = min_gap
                        best_certified_config = final_config.copy()
                

                
                # Always track the best approach seen, even if it failed the -0.2 threshold
                if diag["approach_best_gap"] > best_approach_gap:
                    best_approach_gap = diag["approach_best_gap"]
                    best_approach_config = final_config
                    best_approach_diag = diag
                
                if diag.get("approach_success", False):
                    n_approaches_successful += 1
                else:
                    if first_failure_reason is None:
                        # Best-effort reason extraction
                        reason = diag.get("reason")
                        if reason is None:
                            cert_reason = (diag.get("certification") or {}).get("reason")
                            if cert_reason is not None:
                                reason = f"cert_phase:{cert_reason}"
                            else:
                                mins = (diag.get("trajectory") or {}).get("min_gaps") or []
                                if mins and np.min(mins) < -0.4:
                                    reason = "approach_abort:deep_overlap"
                                else:
                                    reason = "approach_failed"
                        first_failure_reason = str(reason)
            
            # Extract diagnostics from best approach configuration
            best_approach_min_gap = best_approach_gap if best_approach_gap > -np.inf else None
            best_approach_max_rad_err = None
            best_approach_gap_violations = None
            
            # NEW: split gap metrics
            best_approach_min_gap_intruder = None
            best_approach_min_gap_shell = None
            
            if best_approach_config is not None:
                _, rad_err, min_gap, check_diag = check_configuration(
                    best_approach_config, R, cert_eps_r, cert_eps_g
                )
                best_approach_min_gap = min_gap
                best_approach_max_rad_err = rad_err
                best_approach_gap_violations = check_diag["gap_violations"]
                
                # Compute split gaps
                shell_pts = best_approach_config[:-1]
                intr = best_approach_config[-1]
                
                # intruder vs shell
                best_approach_min_gap_intruder = float(
                    np.min(np.linalg.norm(shell_pts - intr, axis=1) - 2.0 * R)
                )
                
                # shell vs shell
                min_shell = np.inf
                for i in range(len(shell_pts)):
                    for j in range(i + 1, len(shell_pts)):
                        gap = np.linalg.norm(shell_pts[i] - shell_pts[j]) - 2.0 * R
                        if gap < min_shell:
                            min_shell = gap
                best_approach_min_gap_shell = float(min_shell)
                
                # Update seed_result best tracking
                if seed_result["best_approach_min_gap"] is None or min_gap > seed_result["best_approach_min_gap"]:
                    seed_result["best_approach_min_gap"] = float(min_gap)
                    seed_result["best_approach_max_rad_err"] = float(rad_err)
                    seed_result["best_approach_gap_violations"] = int(best_approach_gap_violations)
            
            # Record insertion attempt
            insertion_info = {
                "from_N": current_N,
                "to_N": current_N + 1,
                "certified_found": best_certified_config is not None,
                "best_approach_gap": best_approach_gap if best_approach_gap > -np.inf else None,
                "best_approach_min_gap": best_approach_min_gap,
                "best_approach_max_rad_err": best_approach_max_rad_err,
                "best_approach_gap_violations": best_approach_gap_violations,
                
                # NEW fields
                "n_dirs_generated": int(n_dirs_generated),
                "n_dirs_evaluated": int(n_dirs_evaluated),
                "n_approaches_successful": int(n_approaches_successful),
                "first_failure_reason": first_failure_reason,
                "best_approach_min_gap_intruder": best_approach_min_gap_intruder,
                "best_approach_min_gap_shell": best_approach_min_gap_shell,
                
                "failure_stage": None  # Will be set below
            }
            
            # Determine failure stage and handle insertion
            if best_certified_config is not None:
                insertion_info["failure_stage"] = None  # Success
                shell = best_certified_config
                current_N += 1
            elif best_approach_config is None:
                insertion_info["failure_stage"] = "no_path"
                seed_result["insertion_details"].append(insertion_info)
                # No viable path found
                break
            else:
                insertion_info["failure_stage"] = "approach_only"  # Will update if cert_retry fails
                # One more certification attempt with more iterations
                certified_retry, final_config, cert_retry_diag = certify_configuration(
                    best_approach_config, R=R,
                    eps_r=cert_eps_r, eps_g=cert_eps_g,
                    max_iters=cert_iters * 2,  # Double iterations for retry
                    eta=config["cert_eta"] * 0.5  # Smaller steps
                )
                if certified_retry:
                    insertion_info["failure_stage"] = None  # Success after retry
                    shell = final_config
                    current_N += 1
                else:
                    insertion_info["failure_stage"] = "cert_retry_fail"
                    # Capture post-certification diagnostics
                    _, _, best_postcert_min_gap, postcert_diag = check_configuration(
                        final_config, R, cert_eps_r, cert_eps_g
                    )
                    insertion_info["best_postcert_min_gap"] = float(best_postcert_min_gap)
                    # Update seed_result best postcert tracking
                    if seed_result["best_postcert_min_gap"] is None or best_postcert_min_gap > seed_result["best_postcert_min_gap"]:
                        seed_result["best_postcert_min_gap"] = float(best_postcert_min_gap)
                    # Failed to certify - stop
                    seed_result["insertion_details"].append(insertion_info)
                    break
            
            # Append insertion_info for successful cases
            seed_result["insertion_details"].append(insertion_info)
        
        seed_result["achieved_N"] = current_N
        
        # Check if achieved with loose threshold (eps_g = 1e-3)
        loose_eps_g = config.get("loose_eps_g", 1e-3)
        if current_N == N_target:
            is_valid_loose, _, _, _ = check_configuration(
                shell, R, cert_eps_r, loose_eps_g
            )
            seed_result["achieved_loose"] = is_valid_loose
        
        # Final certification check
        if current_N == N_target:
            is_valid, rad_err, min_gap, diag = check_configuration(
                shell, R, cert_eps_r, cert_eps_g
            )
            seed_result["certified"] = is_valid
            seed_result["final_min_gap"] = min_gap
            seed_result["final_radial_error"] = rad_err
            
            if is_valid and config.get("save_configs", False):
                certified_configs.append({
                    "seed": s,
                    "config": shell.tolist(),
                    "min_gap": min_gap
                })
        else:
            seed_result["certified"] = False
            seed_result["final_min_gap"] = np.nan
            seed_result["final_radial_error"] = np.nan
            # Set final failure stage if not already set
            if seed_result["failure_stage"] is None and current_N < N_target:
                # Check insertion_details for last failure stage
                if seed_result["insertion_details"]:
                    last_detail = seed_result["insertion_details"][-1]
                    seed_result["failure_stage"] = last_detail.get("failure_stage", "unknown")
        
        results.append(seed_result)
    
    # Summary
    n_achieved = sum(1 for r in results if r["achieved_N"] == N_target)
    n_certified = sum(1 for r in results if r["certified"])
    n_achieved_loose = sum(1 for r in results if r.get("achieved_loose", False))
    
    summary = {
        "N_target": N_target,
        "n_seeds": n_seeds,
        "n_achieved": n_achieved,
        "n_certified": n_certified,
        "n_achieved_loose": n_achieved_loose,
        "achieved_rate": n_achieved / n_seeds,
        "certified_rate": n_certified / n_seeds,
        "achieved_loose_rate": n_achieved_loose / n_seeds,
        "certified_configs": certified_configs
    }
    
    # Diagnostic statistics
    best_approach_gaps = [r["best_approach_min_gap"] for r in results 
                         if r.get("best_approach_min_gap") is not None]
    if best_approach_gaps:
        summary["best_approach_gap_median"] = float(np.median(best_approach_gaps))
        summary["best_approach_gap_min"] = float(np.min(best_approach_gaps))
        summary["best_approach_gap_max"] = float(np.max(best_approach_gaps))
    
    # Failure stage distribution
    failure_stages = [r.get("failure_stage") for r in results]
    stage_counts = {}
    for stage in failure_stages:
        stage_counts[stage] = stage_counts.get(stage, 0) + 1
    summary["failure_stage_distribution"] = stage_counts
    
    # Gap statistics
    gaps = [r["final_min_gap"] for r in results if np.isfinite(r.get("final_min_gap", np.nan))]
    if gaps:
        summary["gap_median"] = float(np.median(gaps))
        summary["gap_min"] = float(np.min(gaps))
        summary["gap_max"] = float(np.max(gaps))
        summary["gap_std"] = float(np.std(gaps))
    
    if verbose:
        print(f"  N={N_target}: achieved {n_achieved}/{n_seeds}, CERTIFIED {n_certified}/{n_seeds}")
        if gaps:
            print(f"    Gap: median={summary['gap_median']:.2e}, min={summary['gap_min']:.2e}")
    
    return results, summary

def run_diagnostic_suite(config=None, verbose=True):
    """
    Run diagnostic suite for N=41, N=42 with enhanced logging.
    
    Focuses on distinguishing "hard wall" vs "polishing failure" by tracking
    near-miss diagnostics and failure stages.
    """
    if config is None:
        config = CONFIG.copy()
        config["n_seeds"] = config.get("n_seeds_diagnostic", 10)
        config["N_values"] = [41, 42]  # Only test these two
    
    print("=" * 80)
    print("SPRINT 5.7: DIAGNOSTIC RE-RUN (ENHANCED VERSION)")
    print("=" * 80)
    print(f"\nStarted: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"\nConfiguration:")
    print(f"  Seeds per N: {config['n_seeds']} (diagnostic mode)")
    print(f"  Seam directions: {config['K_seams']} (base), {config.get('K_seams_hard', config['K_seams']*2)} (hard)")
    print(f"  Certification tolerance: eps_r = eps_g = {config['cert_eps_r']}")
    print(f"  Loose threshold: eps_g = {config.get('loose_eps_g', 1e-3)}")
    print(f"  N values to test: {config['N_values']}")
    print(f"\nKnown bounds: 40 <= tau_5 <= 44")
    print(f"\nPurpose: Distinguish geometric obstruction vs certification polishing failure")
    print(f"  - Case A (hard wall): best_approach_min_gap < -1e-2")
    print(f"  - Case B (polishing): best_approach_min_gap > -1e-4")
    
    # Create output directory
    output_dir = Path(config.get("output_dir", "./sprint57_results"))
    output_dir.mkdir(exist_ok=True)
    
    all_results = {}
    all_summaries = {}
    
    start_time = time.time()
    
    for N in config["N_values"]:
        print(f"\n{'='*60}")
        print(f"Testing N = {N}")
        print(f"{'='*60}")
        
        n_start = time.time()
        
        results, summary = probe_single_N(
            N_target=N,
            n_seeds=config["n_seeds"],
            K_seams=config["K_seams"],
            config=config,
            seed=42 + N * 1000,
            verbose=verbose
        )
        
        n_elapsed = time.time() - n_start
        print(f"  Time for N={N}: {n_elapsed:.1f}s")
        
        all_results[N] = results
        all_summaries[N] = summary
        
        # Save intermediate results (PRESERVE insertion_details)
        intermediate_path = output_dir / f"results_N{N}.json"
        with open(intermediate_path, 'w') as f:
            json.dump({
                "N": N,
                "summary": summary,
                "results": results  # Keep all fields including insertion_details
            }, f, indent=2, default=str)
    
    total_elapsed = time.time() - start_time
    print(f"\nTotal time: {total_elapsed/60:.1f} minutes")
    
    return all_results, all_summaries

def run_full_certification_suite(config=None, verbose=True):
    """
    Run full certification suite for all N values.
    """
    if config is None:
        config = CONFIG
    
    print("=" * 80)
    print("SPRINT 5.6: CERTIFICATION + FALSIFICATION (FULL VERSION)")
    print("=" * 80)
    print("(Note: This is the original full suite. Use run_diagnostic_suite() for Sprint 5.7)")
    print(f"\nStarted: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"\nConfiguration:")
    print(f"  Seeds per N: {config['n_seeds']}")
    print(f"  Seam directions: {config['K_seams']} (base), {config.get('K_seams_hard', config['K_seams']*2)} (hard)")
    print(f"  Certification tolerance: eps_r = eps_g = {config['cert_eps_r']}")
    print(f"  N values to test: {config['N_values']}")
    print(f"\nKnown bounds: 40 <= tau_5 <= 44")
    print(f"N=45 is FALSIFICATION TEST (must fail if certification is correct)")
    
    # Create output directory
    output_dir = Path(config.get("output_dir", "./sprint56_results"))
    output_dir.mkdir(exist_ok=True)
    
    all_results = {}
    all_summaries = {}
    
    start_time = time.time()
    
    for N in config["N_values"]:
        print(f"\n{'='*60}")
        print(f"Testing N = {N}")
        print(f"{'='*60}")
        
        n_start = time.time()
        
        results, summary = probe_single_N(
            N_target=N,
            n_seeds=config["n_seeds"],
            K_seams=config["K_seams"],
            config=config,
            seed=42 + N * 1000,
            verbose=verbose
        )
        
        n_elapsed = time.time() - n_start
        print(f"  Time for N={N}: {n_elapsed:.1f}s")
        
        all_results[N] = results
        all_summaries[N] = summary
        
        # Save intermediate results (PRESERVE insertion_details)
        intermediate_path = output_dir / f"results_N{N}.json"
        with open(intermediate_path, 'w') as f:
            json.dump({
                "N": N,
                "summary": summary,
                "results": results  # Keep all fields including insertion_details
            }, f, indent=2, default=str)
    
    total_elapsed = time.time() - start_time
    print(f"\nTotal time: {total_elapsed/60:.1f} minutes")
    
    return all_results, all_summaries

def analyze_certification_results(all_summaries, output_dir="./sprint56_results"):
    """
    Comprehensive analysis and plotting of certification results.
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(exist_ok=True)
    
    print("\n" + "=" * 80)
    print("CERTIFICATION RESULTS SUMMARY")
    print("=" * 80)
    
    # Table header
    print(f"\n{'N':>4} {'achieved':>12} {'CERTIFIED':>12} {'gap_median':>14} {'gap_min':>14}")
    print("-" * 60)
    
    for N in sorted(all_summaries.keys()):
        s = all_summaries[N]
        ach_str = f"{s['n_achieved']}/{s['n_seeds']}"
        cert_str = f"{s['n_certified']}/{s['n_seeds']}"
        
        gap_med = s.get('gap_median', np.nan)
        gap_min = s.get('gap_min', np.nan)
        
        gap_med_str = f"{gap_med:.2e}" if np.isfinite(gap_med) else "N/A"
        gap_min_str = f"{gap_min:.2e}" if np.isfinite(gap_min) else "N/A"
        
        print(f"{N:>4} {ach_str:>12} {cert_str:>12} {gap_med_str:>14} {gap_min_str:>14}")
    
    # Plotting
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    Ns = sorted(all_summaries.keys())
    
    # 1. Achieved vs Certified rates
    ax = axes[0, 0]
    achieved = [all_summaries[N]["achieved_rate"] * 100 for N in Ns]
    certified = [all_summaries[N]["certified_rate"] * 100 for N in Ns]
    
    x = np.arange(len(Ns))
    width = 0.35
    
    bars1 = ax.bar(x - width/2, achieved, width, label='Achieved N', 
                   color='steelblue', alpha=0.7, edgecolor='black')
    bars2 = ax.bar(x + width/2, certified, width, label='CERTIFIED', 
                   color='darkgreen', alpha=0.8, edgecolor='black')
    
    ax.set_xlabel("N (target spheres)", fontsize=12)
    ax.set_ylabel("Success Rate (%)", fontsize=12)
    ax.set_title("Achieved vs Certified Success Rates", fontsize=13)
    ax.set_xticks(x)
    ax.set_xticklabels(Ns)
    ax.axhline(y=50, color='gray', linestyle='--', alpha=0.5)
    ax.legend(loc='upper right')
    ax.set_ylim(0, 105)
    ax.grid(True, alpha=0.3, axis='y')
    
    # Mark N=45 specially
    if 45 in Ns:
        idx_45 = Ns.index(45)
        ax.axvline(x=idx_45, color='red', linestyle=':', alpha=0.7, linewidth=2)
        ax.text(idx_45, 95, 'Falsification\n(must fail)', ha='center', fontsize=9, color='red')
    
    # 2. Gap distribution
    ax = axes[0, 1]
    gap_meds = [all_summaries[N].get("gap_median", np.nan) for N in Ns]
    gap_mins = [all_summaries[N].get("gap_min", np.nan) for N in Ns]
    
    valid_mask = [np.isfinite(g) for g in gap_meds]
    if any(valid_mask):
        valid_x = [i for i, v in enumerate(valid_mask) if v]
        valid_meds = [gap_meds[i] for i in valid_x]
        valid_mins = [gap_mins[i] for i in valid_x]
        valid_Ns = [Ns[i] for i in valid_x]
        
        ax.bar([i - width/2 for i in range(len(valid_x))], valid_meds, width, 
               label='Median', color='steelblue', alpha=0.7)
        ax.bar([i + width/2 for i in range(len(valid_x))], valid_mins, width, 
               label='Min', color='darkorange', alpha=0.7)
        ax.set_xticks(range(len(valid_x)))
        ax.set_xticklabels(valid_Ns)
    
    ax.axhline(y=0, color='red', linestyle='-', alpha=0.5, label='Zero (contact)', linewidth=2)
    ax.set_xlabel("N (target spheres)", fontsize=12)
    ax.set_ylabel("Min pairwise gap", fontsize=12)
    ax.set_title("Gap Distribution (certified configs only)", fontsize=13)
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')
    
    # 3. Certification rate curve
    ax = axes[1, 0]
    ax.plot(Ns, certified, 'o-', color='darkgreen', markersize=10, linewidth=2, label='Certified %')
    ax.fill_between(Ns, 0, certified, alpha=0.3, color='green')
    ax.axhline(y=50, color='gray', linestyle='--', alpha=0.5)
    ax.axhline(y=0, color='red', linestyle='-', alpha=0.3)
    ax.set_xlabel("N (target spheres)", fontsize=12)
    ax.set_ylabel("Certification Rate (%)", fontsize=12)
    ax.set_title("Certification Rate vs N", fontsize=13)
    ax.set_xticks(Ns)
    ax.set_ylim(-5, 105)
    ax.grid(True, alpha=0.3)
    
    # 4. Summary statistics
    ax = axes[1, 1]
    ax.axis('off')
    
    # Find key results
    cert_rates = {N: all_summaries[N]["certified_rate"] for N in Ns}
    
    # Wall detection
    wall_N = None
    for N in Ns:
        if cert_rates[N] < 0.1:  # Less than 10% = effective wall
            wall_N = N
            break
    
    # Build summary text
    summary_lines = [
        "SUMMARY",
        "=" * 40,
        "",
        f"Certification tolerance: ε = {CONFIG['cert_eps_r']:.0e}",
        f"Seeds per N: {CONFIG['n_seeds']}",
        f"Seam directions: {CONFIG['K_seams']}",
        "",
        "Results by N:",
    ]
    
    for N in Ns:
        rate = cert_rates[N] * 100
        status = "✓" if rate > 50 else "○" if rate > 0 else "✗"
        summary_lines.append(f"  N={N}: {status} {rate:.0f}% certified")
    
    summary_lines.extend([
        "",
        "-" * 40,
    ])
    
    # Interpretation
    if 45 in cert_rates:
        if cert_rates[45] == 0:
            summary_lines.append("✓ N=45 correctly fails (falsification PASSED)")
        elif cert_rates[45] < 0.1:
            summary_lines.append("⚠ N=45 mostly fails (check tolerance)")
        else:
            summary_lines.append("✗ N=45 succeeds! (tolerance TOO LOOSE)")
    
    if wall_N:
        summary_lines.append(f"\nEffective wall at N = {wall_N}")
        if wall_N <= 44:
            summary_lines.append(f"Consistent with tau_5 <= 44")
        if wall_N == 45:
            summary_lines.append(f"Evidence: tau_5 = 44 (upper bound)")
    
    ax.text(0.05, 0.95, '\n'.join(summary_lines), 
            transform=ax.transAxes, fontsize=11,
            verticalalignment='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.suptitle("Sprint 5.6: Kissing Number Certification Results", fontsize=15, fontweight='bold')
    plt.tight_layout()
    
    # Save plot
    plot_path = output_dir / "sprint57_certification.png"
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to: {plot_path}")
    
    plt.show()
    
    return cert_rates

# =============================================================================
# MAIN ENTRY POINT
# =============================================================================
if __name__ == "__main__":
    # Run diagnostic suite (default for Sprint 5.7)
    all_results, all_summaries = run_diagnostic_suite(
        config=CONFIG,
        verbose=True
    )
    
    # Print diagnostic summary
    print("\n" + "=" * 80)
    print("DIAGNOSTIC SUMMARY")
    print("=" * 80)
    
    for N in sorted(all_summaries.keys()):
        s = all_summaries[N]
        print(f"\nN = {N}:")
        print(f"  Achieved (strict): {s['n_achieved']}/{s['n_seeds']} ({s['achieved_rate']*100:.1f}%)")
        print(f"  Achieved (loose):  {s.get('n_achieved_loose', 0)}/{s['n_seeds']} ({s.get('achieved_loose_rate', 0)*100:.1f}%)")
        print(f"  Certified:         {s['n_certified']}/{s['n_seeds']} ({s['certified_rate']*100:.1f}%)")
        
        if 'best_approach_gap_median' in s:
            print(f"  Best approach gap: median={s['best_approach_gap_median']:.2e}, "
                  f"min={s['best_approach_gap_min']:.2e}, max={s['best_approach_gap_max']:.2e}")
        
        if 'failure_stage_distribution' in s:
            print(f"  Failure stages: {s['failure_stage_distribution']}")
    
    # Analyze and plot
    cert_rates = analyze_certification_results(
        all_summaries,
        output_dir=CONFIG["output_dir"]
    )
    
    # Diagnostic interpretation
    print("\n" + "=" * 80)
    print("DIAGNOSTIC INTERPRETATION")
    print("=" * 80)
    
    for N in sorted(all_summaries.keys()):
        s = all_summaries[N]
        if 'best_approach_gap_median' in s:
            gap_med = s['best_approach_gap_median']
            if gap_med < -1e-2:
                interpretation = "Case A (Hard Wall): Strongly negative gaps suggest geometric obstruction"
            elif gap_med > -1e-4:
                interpretation = "Case B (Polishing Failure): Near-miss gaps suggest certifier too strict"
            else:
                interpretation = "Intermediate: May need continuation schedule"
            
            print(f"\nN = {N}: {interpretation}")
            print(f"  Best approach gap median: {gap_med:.2e}")
            if s.get('achieved_loose_rate', 0) > s['certified_rate']:
                print(f"  Note: achieved_loose ({s.get('achieved_loose_rate', 0)*100:.1f}%) >> certified ({s['certified_rate']*100:.1f}%)")
                print(f"  → Tolerance may be too strict, consider continuation schedule")
    
    # Final interpretation
    print("\n" + "=" * 80)
    print("FINAL INTERPRETATION")
    print("=" * 80)
    
    # Check falsification (only if N=45 was tested)
    if 45 in cert_rates:
        if cert_rates[45] == 0:
            print("\n✓ FALSIFICATION PASSED: N=45 has 0% certification")
            print("  This confirms our constraints are meaningful")
        else:
            print(f"\n⚠ WARNING: N=45 has {cert_rates[45]*100:.1f}% certification")
            print("  Either:")
            print("    1. Certification tolerance is too loose")
            print("    2. We've made a mathematical breakthrough (unlikely)")
            print("  Recommend: tighten eps to 1e-6 and re-run")
    
    # Find highest certified N
    highest_cert = max((N for N in cert_rates if cert_rates[N] > 0.5), default=40)
    print(f"\n📊 Highest N with >50% certification: {highest_cert}")
    
    if highest_cert == 44:
        print("  This matches the known upper bound tau_5 <= 44")
        print("  Strong computational evidence for tau_5 = 44")
    elif highest_cert < 44:
        print(f"  Our optimizer may be too weak (known: tau_5 <= 44)")
    
    # Save final summary
    output_dir = Path(CONFIG["output_dir"])
    final_summary = {
        "config": {k: v for k, v in CONFIG.items() if k != "N_values"},
        "N_values": CONFIG["N_values"],
        "certification_rates": {str(N): float(r) for N, r in cert_rates.items()},
        "summaries": {str(N): {k: v for k, v in s.items() if k != "certified_configs"} 
                      for N, s in all_summaries.items()},
        "interpretation": {
            "falsification_passed": cert_rates.get(45, 1) == 0,
            "highest_certified_N": highest_cert,
            "consistent_with_bound": highest_cert <= 44
        }
    }
    
    summary_path = output_dir / "sprint57_final_summary.json"
    with open(summary_path, 'w') as f:
        json.dump(final_summary, f, indent=2, default=str)
    print(f"\nFinal summary saved to: {summary_path}")
    
    print("\n" + "=" * 80)
    print("SPRINT 5.7 DIAGNOSTIC COMPLETE")
    print("=" * 80)
    print("\nNext steps:")
    print("  - Review best_approach_min_gap values to distinguish Case A vs Case B")
    print("  - If Case B dominates: Implement Sprint 5.8 (certification continuation)")
    print("  - If Case A dominates: Consider Sprint 5.9 (search-space falsification)")