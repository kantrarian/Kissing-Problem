"""Sprint 5.11-D: Max Clique Search (Szöllősi's Method)"""
import numpy as np
import networkx as nx
from sprint59c_control_first import random_shell


def find_max_clique_dense(n_candidates=5000, d=5, R=1.0, seed=42):
    """
    Denser sampling with multiple strategies: Pure Random, Lattice-like (D5), and Perturbed.
    """
    rng = np.random.default_rng(seed)
    
    print(f"Generating {n_candidates} candidate points (Dense + Structural)...")
    
    # Strategy 1: Pure random
    X1 = rng.normal(size=(n_candidates // 3, d))
    X1 /= np.linalg.norm(X1, axis=1, keepdims=True)
    
    # Strategy 2: Lattice-like points (D5 roots)
    from itertools import combinations, product
    lattice_pts = []
    # D5 roots: permutations of (+/-1, +/-1, 0, 0, 0)
    base = [1, 1, 0, 0, 0]
    from itertools import permutations
    for perm in set(permutations(base)):
        nonzero = [i for i, x in enumerate(perm) if x != 0]
        for signs in product([-1, 1], repeat=2):
            pt = list(perm)
            pt[nonzero[0]] *= signs[0]
            pt[nonzero[1]] *= signs[1]
            lattice_pts.append(pt)
    
    X2 = np.array(lattice_pts)
    X2 = X2 / np.linalg.norm(X2, axis=1, keepdims=True)
    
    # Strategy 3: Perturbed lattice
    # Create many perturbed copies to explore neighborhood of D5
    n_perturbed = n_candidates - len(X1) - len(X2)
    # Sample randomly from X2 then add noise
    indices = rng.choice(len(X2), size=n_perturbed)
    X3 = X2[indices] + rng.normal(size=(n_perturbed, d)) * 0.1
    X3 /= np.linalg.norm(X3, axis=1, keepdims=True)
    
    # Combine
    X = np.vstack([X1, X2, X3])
    # Remove duplicates (within tolerance) to keep graph size manageable
    # Simple quantization for unique check
    # X_quant = np.round(X, 6)
    # _, unique_idx = np.unique(X_quant, axis=0, return_index=True)
    # X = X[unique_idx]
    
    print(f"Total unique candidates: {len(X)}")
    
    print("Building compatibility graph (edges for angle >= 60 deg)...")
    # Inner product <= 0.5 means angle >= 60
    # G_ij = x_i . x_j
    G = X @ X.T
    
    # Adjacency matrix: 1 if compatible (separation >= 60), else 0
    # cos(60) = 0.5. So compatible if dot_product <= 0.500001 (tolerance)
    adj = (G <= 0.50001)
    np.fill_diagonal(adj, 0) # No self loops
    
    # Convert to NetworkX
    graph = nx.from_numpy_array(adj)
    
    print(f"Graph stats: {graph.number_of_nodes()} nodes, {graph.number_of_edges()} edges")
    
    # Heuristic clique search first
    print("Running heuristic clique search...")
    clique = nx.algorithms.clique.max_weight_clique(graph, weight=None)
    size = len(clique[0])
    print(f"Max Clique Size found: {size}")
    
    if size >= 41:
        print("*** FOUND N=41 PACKING via Clique Search! ***")
        nodes = list(clique[0])
        packing = X[nodes]
        np.save("sprint511_clique_packing.npy", packing)
    else:
        print("Did not find N=41. Best was N={size}.")
        
    return size

if __name__ == "__main__":
    find_max_clique_dense()
