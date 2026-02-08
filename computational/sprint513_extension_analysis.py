"""Sprint 5.13 Extension Analysis: Finding the Best Discrete Gap"""
import numpy as np

def analyze_extensions():
    print("Loading candidates...")
    X = np.load("sprint513_candidates.npy")
    N, d = X.shape
    print(f"Loaded {N} candidates.")
    
    # 1. Identify the D5 clique (Control)
    # Strategy: We know D5 are the first ~40 from generation, or we can use signature
    # Let's find exactly the 40 points that form the D5 clique
    from sprint513_clique_solver import d5_signature_score
    
    d5_indices = [i for i in range(N) if d5_signature_score(X[i])]
    d5_indices = np.array(d5_indices)
    
    print(f"Identified {len(d5_indices)} D5-like points in candidates.")
    if len(d5_indices) < 40:
        print("Error: Could not find full D5 set.")
        return
        
    # Verify they form a clique
    C = X[d5_indices]
    G = C @ C.T
    np.fill_diagonal(G, -1.0)
    max_internal_cos = np.max(G)
    if max_internal_cos > 0.5 + 1e-6:
        print(f"Warning: D5 set has internal violation: {max_internal_cos}")
    else:
        print("D5 set verified as valid 40-clique.")
        
    # 2. Analyze Extension Candidates
    # For every candidate v NOT in D5, compute max(v . c) for c in D5
    # We want to minimize this max value (make it <= 0.5)
    
    # Identify non-D5 candidates
    all_indices = set(range(N))
    extension_indices = list(all_indices - set(d5_indices))
    
    if not extension_indices:
        print("No extension candidates found!")
        return
        
    E = X[extension_indices]
    print(f"Analyzing {len(E)} extension candidates...")
    
    # Compute dot products: E (M x d) @ C.T (d x 40) -> (M x 40)
    Dots = E @ C.T
    
    # Max cosine for each candidate against the clique
    max_cos_per_cand = np.max(Dots, axis=1)
    
    # We want the candidate that has the *smallest* max_cos (closest to being compatible)
    best_idx_local = np.argmin(max_cos_per_cand)
    best_max_cos = max_cos_per_cand[best_idx_local]
    best_candidate_idx = extension_indices[best_idx_local]
    
    # Gap calculation
    # Discrete Gap = 0.5 - MaxCos (Positive = Compatible)
    discrete_gap = 0.5 - best_max_cos
    
    # Distance Gap
    # g_min = 2*sqrt(2 - 2*cos) - 2
    from sprint513_clique_solver import min_distance_gap_from_maxcos
    dist_gap = min_distance_gap_from_maxcos(best_max_cos)
    
    print("\n=== Extension Analysis Results ===")
    print(f"Best Extension Candidate Index: {best_candidate_idx}")
    print(f"Max Cosine with D5: {best_max_cos:.6f}")
    print(f"Target Cosine:      0.500000")
    print(f"Discrete Gap:       {discrete_gap:.6f} (Positive = Valid Extension)")
    print(f"Equivalent Dist Gap:{dist_gap:.6f}")
    print("--------------------------------")
    
    if discrete_gap >= 0:
        print("*** BREAKTHROUGH: Found compatible extension! N=41 exists in this set! ***")
    else:
        print("Result: No extension found.")
        print(f"Closest candidate is still {abs(dist_gap):.6f} distance units away.")

if __name__ == "__main__":
    analyze_extensions()
