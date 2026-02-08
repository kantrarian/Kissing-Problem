"""Sprint 5.11-C: Gram Matrix Optimization (Coordinate Free)"""
import numpy as np
import scipy.optimize

def solve_gram_optimization_enhanced(N=41, d=5, n_seeds=50):
    """
    Enhanced Factorized Gram Optimization (Burer-Monteiro style).
    - Multiple seeds (50)
    - Alpha annealing (5 -> 50) for LSE sharpness
    """
    rng = np.random.default_rng(42)  # Fixed master seed
    
    best_overall_gap = -np.inf
    best_overall_cos = 1.0
    
    # Revert to single-stage optimization (worked best in 5.11-C)
    alpha = 20.0
    
    print(f"Enhanced Factorized Gram Optimization (N={N}, d={d})")
    print(f"Seeds: {n_seeds}, Fixed Alpha: {alpha} (Numerical Gradients)")
    print("=" * 60)
    
    for seed in range(n_seeds):
        seed_rng = np.random.default_rng(seed)
        V = seed_rng.normal(size=(N, d))
        V = V / np.linalg.norm(V, axis=1, keepdims=True)
        v_flat = V.flatten()
        
        def objective(v_input):
            V_curr = v_input.reshape((N, d))
            norms = np.linalg.norm(V_curr, axis=1, keepdims=True)
            V_norm = V_curr / (norms + 1e-12)
                
            G = V_norm @ V_norm.T
            mask = ~np.eye(N, dtype=bool)
                
            # LogSumExp
            max_val = np.max(G[mask])
            shifted = alpha * (G[mask] - max_val)
            lse = max_val + np.log(np.sum(np.exp(shifted))) / alpha
            
            return lse

        res = scipy.optimize.minimize(
            objective, 
            v_flat, 
            method='L-BFGS-B',
            jac=False,
            options={'maxiter': 5000, 'ftol': 1e-9}
        )
        v_flat = res.x
            
        # Final evaluation for this seed
        V_final = v_flat.reshape((N, d))
        V_final /= np.linalg.norm(V_final, axis=1, keepdims=True)
        G_final = V_final @ V_final.T
        mask = ~np.eye(N, dtype=bool)
        max_cos = np.max(G_final[mask])
        gap = 0.5 - max_cos
        
        if gap > best_overall_gap:
            best_overall_gap = gap
            best_overall_cos = max_cos
            print(f"Seed {seed:2d}: New Best Gap = {gap:.6f} (Cos={max_cos:.6f})")
            
        if gap >= -1e-5:
            print(f"*** CERTIFIED at seed {seed}! Gap: {gap:.6f} ***")
            return best_overall_gap
            
    print("\noptimization Complete.")
    print(f"Best Gap: {best_overall_gap:.6f} (Target > 0.0)")
    print(f"Max Cos:  {best_overall_cos:.6f}")
    
    return best_overall_gap

if __name__ == "__main__":
    solve_gram_optimization_enhanced()
