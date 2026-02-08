"""Sprint 5.14: Targeted Refinement of Best N=41 Candidate"""
import numpy as np
import time
from sprint59c_control_first import (
    repair_then_polish, 
    OptParams, 
    min_gap
)

def refine_best_candidate():
    print(f"\n{'='*60}")
    print(f"High-Precision Refinement: N=41, d=5")
    print(f"{'='*60}")
    
    # Load previously found best point (-0.036 basin)
    try:
        x0 = np.load("sprint59c_best_N41.npy")
        print("Loaded 'sprint59c_best_N41.npy' successfully.")
    except FileNotFoundError:
        print("Error: 'sprint59c_best_N41.npy' not found! Cannot refine.")
        return

    # Check current gap
    current_gap = min_gap(x0, R=1.0)
    print(f"Starting Gap: {current_gap:.9f}")

    # Strict parameters for high precision refinement
    params = OptParams(
        repair_iters=5000,      # Short repair to stabilize
        repair_tau=0.05,
        
        polish_iters=150000,    # Very deep polish
        polish_eta=0.001,       # Fine steps
        polish_tau0=0.05,
        polish_tau_decay=0.9999,
        polish_tau_min=1e-10,   # Extreme precision target
        max_step_norm=0.005
    )
    
    print("Running optimization (target precision 1e-10)...")
    t0 = time.time()
    
    res = repair_then_polish(x0, R=1.0, params=params, eps_g=1e-12, eps_r=1e-12)
    
    final_gap = res["final_min_gap"]
    duration = time.time() - t0
    
    print("-" * 60)
    print(f"Refinement Complete (Time: {duration:.1f}s)")
    print(f"Final Gap: {final_gap:.12f}")
    
    # Hypothesis Checking
    formula1 = -np.pi / (40 * 10**(1/3))  # -0.03645...
    formula2 = np.cos(2 - np.pi/8)        # -0.03650...
    
    print(f"\nHypothesis Comparison:")
    print(f"F1 (Kissing Scaling): {formula1:.12f}")
    print(f"F2 (Angular Offset):  {formula2:.12f}")
    
    err1 = abs(final_gap - formula1)
    err2 = abs(final_gap - formula2)
    
    print(f"\nError F1: {err1:.9f}")
    print(f"Error F2: {err2:.9f}")
    
    if err1 < err2:
        print(">> Result favors Formula 1 (Kissing Scaling).")
    else:
        print(">> Result favors Formula 2 (Angular Offset).")
        
    # Also print the d=4 result we found earlier
    d4_res = -0.082539269762
    pred_d4 = -0.0720
    print(f"\nRecalling d=4 Control (N=25):")
    print(f"Empirical: {d4_res:.9f}")
    print(f"Predicted: {pred_d4:.9f}")
    print(f"Error:     {abs(d4_res - pred_d4):.9f}")

if __name__ == "__main__":
    refine_best_candidate()
