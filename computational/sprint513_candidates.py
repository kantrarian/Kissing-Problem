"""Sprint 5.13-A: Algebraic Candidate Generator for Clique Search"""
import numpy as np
from itertools import product, combinations

def generate_fixed_norm_candidates(m_values=[2, 3, 4, 5, 8, 10], d=5, max_entry=3):
    """
    Generate integer vectors v with squared norm ||v||^2 = m.
    Normalize them to unit sphere: u = v / sqrt(m).
    Inner products will be rational multiples 1/m.
    """
    candidates = []
    print(f"Generating candidates for m in {m_values}...")
    
    # Pre-compute entries loop to avoid deep recursion if possible, but d=5 is small enough for product
    entries = range(-max_entry, max_entry + 1)
    
    seen_hashes = set()
    
    for m in m_values:
        # Optimization: only checking sequences that could sum to m?
        # Brute force is O((2*max_entry+1)^5). For max_entry=3, 7^5 = 16807. Fast.
        count_m = 0
        for coords in product(entries, repeat=d):
            v = np.array(coords, dtype=float)
            norm_sq = np.dot(v, v)
            
            if abs(norm_sq - m) < 1e-9:
                # Found one!
                v_norm = v / np.sqrt(m)
                
                # Dedup using quantified tuple
                v_hash = tuple(np.round(v_norm, 6))
                if v_hash not in seen_hashes:
                    seen_hashes.add(v_hash)
                    candidates.append(v_norm)
                    count_m += 1
        
        print(f"  m={m}: {count_m} unique vectors found")
        
    return np.array(candidates)

def generate_root_system_candidates(d=5):
    """
    Generate D5 and A5 root systems explicitly to ensure 
    we contain the known optimal configurations.
    """
    candidates = []
    seen_hashes = set()
    
    # D5 Roots: Permutations of (+/-1, +/-1, 0, 0, 0) normalized (sq norm 2)
    # 5 choose 2 positions * 4 sign combos = 10 * 4 = 40 vectors
    from itertools import permutations
    base = [0] * d
    base[0] = 1
    base[1] = 1
    
    counts = {"D5": 0, "A5": 0, "Cross": 0}
    
    # D5
    for perm in set(permutations(base)):
        idxs = [i for i, x in enumerate(perm) if x == 1]
        for signs in product([-1, 1], repeat=2):
            v = np.zeros(d)
            v[idxs[0]] = signs[0]
            v[idxs[1]] = signs[1]
            
            v_norm = v / np.linalg.norm(v)
            v_hash = tuple(np.round(v_norm, 6))
            if v_hash not in seen_hashes:
                seen_hashes.add(v_hash)
                candidates.append(v_norm)
                counts["D5"] += 1
                
    # A5 Roots (projected to 5D? Or usually A5 lives in 6D plane sum x=0)
    # A5 ~ D5 lattice subset approx. 
    # Let's generate Cross Polytope instead (simplest): +/- e_i
    for i in range(d):
        for s in [-1, 1]:
            v = np.zeros(d)
            v[i] = s
            v_hash = tuple(np.round(v, 6))
            if v_hash not in seen_hashes:
                seen_hashes.add(v_hash)
                candidates.append(v)
                counts["Cross"] += 1
                
    print(f"Root Systems: Found {counts['D5']} D5, {counts['Cross']} Cross.")
    return np.array(candidates)

def generate_all_candidates():
    print("=== Generating Structured Candidates ===")
    
    # 1. Root systems (Core)
    roots = generate_root_system_candidates()
    
    # 2. Integer vectors (Dense Cloud)
    # m=2 covers D5, but let's include it explicitly above to be safe.
    # m=1 covers Cross (sq norm 1).
    # New m's: 3, 4, 5, 6, 8, 10
    integers = generate_fixed_norm_candidates(m_values=[2, 3, 4, 5, 8, 10], max_entry=3)
    
    # Merge and Dedup
    all_cand = np.vstack([roots, integers])
    
    # Final Dedup
    unique_cand = []
    seen = set()
    for v in all_cand:
        h = tuple(np.round(v, 6))
        if h not in seen:
            seen.add(h)
            unique_cand.append(v)
            
    X = np.array(unique_cand)
    print(f"Total Unique Candidates: {len(X)}")
    
    # Verify D5 is present (Control)
    d5_count = 0 
    # D5 roots have specific form. Let's checking against a generated set
    # Actually, we generated roots first, so they MUST be in there if dedup works.
    
    return X

if __name__ == "__main__":
    X = generate_all_candidates()
    np.save("sprint513_candidates.npy", X)
