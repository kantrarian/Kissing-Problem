"""Sprint 5.14: High-Precision Gap Refinement"""
import numpy as np
import time
from sprint59c_control_first import (
    repair_then_polish, 
    OptParams, 
    random_shell, 
    min_gap,
    d5_shell_points
)

def run_precision_experiment(N, d, restarts=10, formula_target=None):
    print(f"\n{'='*60}")
    print(f"High-Precision Check: N={N}, d={d}")
    if formula_target:
        print(f"Formula Prediction: {formula_target:.9f}")
    print(f"{'='*60}")
    
    # Strict parameters for high precision
    # Increase iterations and reduce tau for sharper max-min
    params = OptParams(
        repair_iters=30000,     # Ensure getting into good basin
        polish_iters=100000,    # Deep polish
        polish_eta=0.002,       # Slower learning rate
        polish_tau_decay=0.9999,# Slower annealing
        polish_tau_min=1e-6,    # Very sharp approximation
        max_step_norm=0.01
    )
    
    rng = np.random.default_rng(42)
    R = 1.0
    
    best_gap = -np.inf
    best_points = None
    
    for r in range(restarts):
        t0 = time.time()
        
        # For N=41 d=5, inject D5 seed occasionally to ensure we are in the right neighborhood?
        # Actually random starts usually find the -0.036 attraction basin easily.
        x0 = random_shell(N, d, R, rng)
        
        # Run optimization
        # Use very loose epsilon check so it runs full duration?
        # Or just let it run.
        res = repair_then_polish(x0, R, params, eps_g=1e-9, eps_r=1e-9)
        
        final_gap = res["final_min_gap"]
        duration = time.time() - t0
        
        print(f"Run {r+1}/{restarts}: Gap = {final_gap:.12f} (Time: {duration:.1f}s)")
        
        if final_gap > best_gap:
            best_gap = final_gap
            best_points = res["final_points"]
            
    print("-" * 60)
    print(f"Best Gap for N={N}, d={d}: {best_gap:.12f}")
    if formula_target:
        error = abs(best_gap - formula_target)
        pct_err = (error / abs(formula_target)) * 100
        print(f"Difference from Prediction: {error:.9f} ({pct_err:.4f}%)")
        
    return best_gap

if __name__ == "__main__":
    # 1. Dimension 4 Control (N=25)
    # Prediction: -0.0720...
    pred_d4 = -0.0720 # Approx
    g4 = run_precision_experiment(N=25, d=4, restarts=5, formula_target=pred_d4)
    
    # 2. Dimension 5 Target (N=41)
    # Candidates:
    # Formula 1: -0.036453
    # Formula 2: -0.036503
    formula1_g5 = -np.pi / (40 * 10**(1/3))
    formula2_g5 = np.cos(2 - np.pi/8)
    
    print(f"\nTarget Candidates d=5:")
    print(f"F1 (Kissing Scaling): {formula1_g5:.12f}")
    print(f"F2 (Angular Offset):  {formula2_g5:.12f}")
    
    g5 = run_precision_experiment(N=41, d=5, restarts=10, formula_target=formula1_g5)
    
    # Final Comparison
    print("\n" + "="*60)
    print("FINAL HYPOTHESIS CHECK")
    print("="*60)
    
    print(f"d=4 Control (N=25): {g4:.12f}")
    d4_err = abs(g4 - (-0.0720)) # Rough check
    print(f"d=5 Target  (N=41): {g5:.12f}")
    
    f1_err = abs(g5 - formula1_g5)
    f2_err = abs(g5 - formula2_g5)
    
    print(f"F1 Error (d=5): {f1_err:.9f}")
    print(f"F2 Error (d=5): {f2_err:.9f}")
    
    if f1_err < f2_err:
        print(">> Formula 1 is the better fit.")
    else:
        print(">> Formula 2 is the better fit.")
