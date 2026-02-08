"""Sprint 5.15: Universal Dimensionality Check (d=3 to d=7)"""
import numpy as np
import time
import json
from sprint59c_control_first import (
    repair_then_polish, 
    OptParams, 
    random_shell,
    min_gap
)

def run_dimension_sweep():
    # Proven kissing numbers tau_d
    # d: (tau_d, known_status)
    targets = {
        3: 12,
        4: 24,
        5: 40,
        6: 72, 
        7: 126
    }
    
    # Parameters for the sweep
    # Enough to converge, but not excessive
    params = OptParams(
        repair_iters=20000,
        polish_iters=30000,
        polish_eta=0.005,
        polish_tau_min=1e-8
    )
    
    n_restarts = 5 # Should be enough if method is robust
    rng = np.random.default_rng(42)
    R = 1.0
    
    results = {}
    
    print(f"{'='*60}")
    print(f"Sprint 5.15: Universal Dimensionality Check (d=3..7)")
    print(f"{'='*60}")
    
    for d, tau in targets.items():
        print(f"\n--- Dimension {d} (Tau={tau}) ---")
        
        # Test Case 1: N = Tau (Control - Should Succeed)
        n_control = tau
        print(f"Testing N={n_control} (Expect Feasible)...")
        best_gap_control = -np.inf
        
        for r in range(n_restarts):
            x0 = random_shell(n_control, d, R, rng)
            res = repair_then_polish(x0, R, params, eps_g=1e-8, eps_r=1e-8)
            gap = res["final_min_gap"]
            
            if gap > best_gap_control:
                best_gap_control = gap
                
            if gap >= -1e-8:
                print(f"  Run {r+1}: SUCCESS (Gap={gap:.9f})")
                best_gap_control = gap
                break # Found valid config
            else:
                print(f"  Run {r+1}: Gap={gap:.9f}")
                
        # Test Case 2: N = Tau + 1 (Falsification - Should Fail)
        n_fail = tau + 1
        print(f"Testing N={n_fail} (Expect Infeasible)...")
        best_gap_fail = -np.inf
        
        for r in range(n_restarts):
            x0 = random_shell(n_fail, d, R, rng)
            res = repair_then_polish(x0, R, params, eps_g=1e-8, eps_r=1e-8)
            gap = res["final_min_gap"]
            
            if gap > best_gap_fail:
                best_gap_fail = gap
                
            print(f"  Run {r+1}: Gap={gap:.9f}")
        
        # Summarize Dimension
        status_control = "PASS" if best_gap_control > -1e-5 else "FAIL"
        status_fail = "PASS" if best_gap_fail < -1e-5 else "FAIL" # "PASS" means we failed to find 41, which is good
        
        print(f"Summary d={d}:")
        print(f"  N={n_control}: Best Gap = {best_gap_control:.6f} [{status_control}]")
        print(f"  N={n_fail}: Best Gap = {best_gap_fail:.6f} [{status_fail}]")
        
        results[d] = {
            "tau": tau,
            "control_gap": best_gap_control,
            "fail_test_gap": best_gap_fail
        }
        
    # Final Report
    print("\n" + "="*60)
    print("CROSS-DIMENSION VALIDATION REPORT")
    print("="*60)
    print(f"{'Dim':<5} | {'Tau':<5} | {'Control Gap':<15} | {'N+1 Gap':<15} | {'Verdict':<10}")
    print("-" * 65)
    
    for d, data in results.items():
        c_gap = data["control_gap"]
        f_gap = data["fail_test_gap"]
        
        # Verdict: Control must be >= 0 (approx), Fail must be < 0
        is_valid = (c_gap > -1e-4) and (f_gap < -1e-4)
        verdict = "VALID" if is_valid else "ISSUE"
        
        print(f"{d:<5} | {data['tau']:<5} | {c_gap:<15.6f} | {f_gap:<15.6f} | {verdict:<10}")
        
    with open("sprint515_results.json", "w") as f:
        json.dump(results, f, indent=2)

if __name__ == "__main__":
    run_dimension_sweep()
