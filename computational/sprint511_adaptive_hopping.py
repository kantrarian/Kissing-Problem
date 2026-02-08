"""Sprint 5.11-A: Adaptive Basin Hopping"""
import numpy as np
import json
import time
from dataclasses import dataclass
from sprint59c_control_first import (
    project_all, random_shell, repair_then_polish, OptParams
)

@dataclass
class AdaptiveHoppingParams:
    n_hops: int = 500
    T_init: float = 0.02
    T_min: float = 0.001
    T_decay: float = 0.995
    step_size_init: float = 0.3
    target_accept_min: float = 0.20
    target_accept_max: float = 0.40
    window_size: int = 20

def run_adaptive_hopping(N=41, d=5, R=1.0, params=AdaptiveHoppingParams(), seed=42):
    rng = np.random.default_rng(seed)
    
    current_x = random_shell(N, d, R, rng)
    
    # Initial minimization
    opt_params = OptParams(repair_iters=3000, polish_iters=5000)
    res = repair_then_polish(current_x, R, opt_params, 1e-5, 1e-5)
    current_x = res["final_points"]
    current_gap = res["final_min_gap"]
    
    best_x = current_x.copy()
    best_gap = current_gap
    
    # Adaptive state
    T = params.T_init
    step_size = params.step_size_init
    history = []
    recent_accepts = []
    
    print(f"Starting Adaptive Hopping (N={N}, T_init={T}, step={step_size})")
    
    for step in range(params.n_hops):
        # 1. Perturb
        noise = rng.normal(size=current_x.shape)
        # Tangent projection
        norms = np.linalg.norm(current_x, axis=1, keepdims=True)
        xhat = current_x / norms
        radial = np.sum(noise * xhat, axis=1, keepdims=True) * xhat
        tangent_noise = (noise - radial) * step_size
        proposal_x = project_all(current_x + tangent_noise, 2.0*R)
        
        # 2. Minimize
        res = repair_then_polish(proposal_x, R, opt_params, 1e-5, 1e-5)
        new_x = res["final_points"]
        new_gap = res["final_min_gap"]
        
        # 3. Metropolis
        delta_E = current_gap - new_gap # We maximize gap (minimize -gap)
        accept = False
        if delta_E < 0:
            accept = True
        else:
            if rng.random() < np.exp(-delta_E / T):
                accept = True
                
        if res["certified"]:
            print(f"*** CERTIFIED at hop {step}! Gap: {new_gap:.6f}")
            return new_gap, history
            
        if accept:
            current_x = new_x
            current_gap = new_gap
            recent_accepts.append(1)
        else:
            recent_accepts.append(0)
            
        if new_gap > best_gap:
            best_gap = new_gap
            best_x = new_x.copy()
            print(f"  New Best at hop {step}: {best_gap:.6f}")
            
        # 4. Adapt
        if len(recent_accepts) > params.window_size:
            recent_accepts.pop(0)
            rate = sum(recent_accepts) / len(recent_accepts)
            
            if rate < params.target_accept_min:
                T *= 1.05 # Heat up
                step_size *= 0.95 # Smaller steps
            elif rate > params.target_accept_max:
                T *= 0.95 # Cool down
                step_size *= 1.05 # Larger steps
                
            T = max(T, params.T_min)

        if (step+1) % 20 == 0:
            rate = sum(recent_accepts)/len(recent_accepts) if recent_accepts else 0
            print(f"Hop {step+1}: best={best_gap:.6f}, curr={current_gap:.6f}, rate={rate:.2f}, T={T:.4f}")
            
        history.append({"step": step, "gap": new_gap, "best": best_gap, "T": T})
        
    return best_gap, history

if __name__ == "__main__":
    run_adaptive_hopping()
