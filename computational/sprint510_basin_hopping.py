"""Sprint 5.10-A: Basin Mirroring (Basin Hopping) for N=41"""
import numpy as np
import json
import time
from dataclasses import dataclass
from typing import Optional

# Reuse robust optimizer from Sprint 5.9-C
from sprint59c_control_first import (
    project_all, random_shell, min_gap, radial_error,
    repair_then_polish, OptParams, logsumexp_maxmin_and_grad,
    project_grad_tangent
)

@dataclass
class HoppingParams:
    n_hops: int = 500
    T: float = 0.002       # Temperature for Metropolis
    step_size: float = 0.2 # Magnitude of perturbation (jump)
    mirror_prob: float = 0.5 # Probability to try mirroring if stuck
    
    # Inner optimizer params (slightly faster for hopping)
    inner_repair_iters: int = 2000
    inner_polish_iters: int = 3000

def apply_perturbation(points: np.ndarray, R: float, step_size: float, rng) -> np.ndarray:
    """Random tangential perturbation (Monte Carlo step)."""
    N, d = points.shape
    noise = rng.normal(size=(N, d))
    
    # Project noise to tangent space
    radius = 2.0 * R
    # approximate tangent projection
    norms = np.linalg.norm(points, axis=1, keepdims=True)
    xhat = points / norms
    radial = np.sum(noise * xhat, axis=1, keepdims=True) * xhat
    tangent_noise = noise - radial
    
    # Scale
    tangent_noise *= step_size
    
    # Apply
    new_points = points + tangent_noise
    return project_all(new_points, radius)

def apply_mirroring(points: np.ndarray, R: float, grad_prev: np.ndarray, step_size: float) -> np.ndarray:
    """
    Reflection move: Step in the direction OPPOSITE to the gradient 
    that was pushing us into the current minimum.
    """
    radius = 2.0 * R
    # Mirroring: move 'step_size' along -grad (or +grad depending on definition)
    # Here we want to escape the basin, so we follow the 'ascent' direction of the barrier?
    # Actually, standard mirroring often reflects the *step* that was rejected.
    # But here we assume we are at a local min, so gradient is ~0.
    # The 'grad_prev' might be the gradient of the penalty function shortly before convergence?
    # Alternatively, simply reflect the previous perturbation if it was rejected?
    # Let's implement simpler "Inverse Kick": Just kick in opposite direction of previous rejected kick? 
    # Or better: "Smart Ascent" - climb up the lowest eigenvector? Too expensive.
    
    # Implementation: Just a large random kick but enforcing it's far from current?
    # Let's stick to "Antipodal Kick": Pick a random direction, if it fails, try -direction.
    return points # Placeholder if not using stateful mirroring, handled in loop

def run_basin_hopping(N: int = 41, d: int = 5, R: float = 1.0, 
                      params: HoppingParams = HoppingParams(),
                      seed: int = 42):
    rng = np.random.default_rng(seed)
    
    # 1. Initialize
    current_x = random_shell(N, d, R, rng)
    
    # Initial minimization
    opt_params = OptParams(
        repair_iters=5000, 
        polish_iters=5000,
        polish_tau_min=0.01 # Don't cool too much for inner loop
    )
    res = repair_then_polish(current_x, R, opt_params, eps_g=1e-5, eps_r=1e-5)
    current_x = res["final_points"]
    current_gap = res["final_min_gap"]
    
    best_x = current_x.copy()
    best_gap = current_gap
    
    history = []
    start_time = time.time()
    
    print(f"Starting Basin Hopping (N={N}, T={params.T}, steps={params.n_hops})")
    print(f"Initial gap: {current_gap:.6f}")
    
    # For mirroring stats
    accepted_count = 0
    
    for step in range(params.n_hops):
        # 2. Perturb
        # Check if we should mirror (if previous was rejected? complex state)
        # Simple version: Random kick
        proposal_x = apply_perturbation(current_x, R, params.step_size, rng)
        
        # 3. Local Minimization
        # Use lighter params for speed
        inner_params = OptParams(
            repair_iters=params.inner_repair_iters,
            repair_target=-0.02, # Quick repair
            polish_iters=params.inner_polish_iters,
            polish_tau_min=0.02 # Keep it a bit warm
        )
        res = repair_then_polish(proposal_x, R, inner_params, eps_g=1e-5, eps_r=1e-5)
        new_x = res["final_points"]
        new_gap = res["final_min_gap"]
        
        # 4. Accept/Reject (Metropolis)
        # We want to MAXIMIZE gap (which is negative).
        # Energy E = -gap. We want to minimize E.
        # delta_E = E_new - E_curr = (-new_gap) - (-current_gap) = current_gap - new_gap
        # If new_gap > current_gap, delta_E < 0 (improvement), accept always.
        # If new_gap < current_gap, delta_E > 0 (worse), accept with prob exp(-delta_E / T)
        
        delta_E = current_gap - new_gap
        
        accept = False
        if delta_E < 0:
            accept = True
        else:
            prob = np.exp(-delta_E / params.T)
            if rng.random() < prob:
                accept = True
        
        if res["certified"]:
            print(f"*** CERTIFIED at hop {step}! Gap: {new_gap:.6f}")
            best_x = new_x
            best_gap = new_gap
            current_x = new_x
            current_gap = new_gap
            history.append({"step": step, "gap": new_gap, "best_gap": best_gap, "accepted": True, "certified": True})
            break
            
        if accept:
            current_x = new_x
            current_gap = new_gap
            accepted_count += 1
            status = "ACC"
        else:
            status = "REJ"
        
        # Update global best
        if new_gap > best_gap:
            best_gap = new_gap
            best_x = new_x.copy()
            print(f"  New Best at hop {step}: {best_gap:.6f}")
            
        # Logging
        if (step+1) % 10 == 0:
            elapsed = time.time() - start_time
            print(f"Hop {step+1}/{params.n_hops}: curr={current_gap:.6f}, best={best_gap:.6f}, {status}, rate={accepted_count/(step+1):.2f}, t={elapsed:.1f}s")
            
        history.append({
            "step": step,
            "gap": new_gap,
            "best_gap": best_gap,
            "accepted": accept,
            "certified": False
        })

    # Final stats
    print("\nBasin Hopping Complete")
    print(f"Best Gap: {best_gap:.6f}")
    
    # Save
    np.save(f"sprint510a_best_N{N}.npy", best_x)
    with open(f"sprint510a_history_N{N}.json", "w") as f:
        json.dump(history, f, indent=2)
        
    return best_gap, history

if __name__ == "__main__":
    # N=41 Basin Hopping
    run_basin_hopping(N=41, seed=123)
