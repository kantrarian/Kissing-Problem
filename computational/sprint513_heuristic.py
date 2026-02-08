"""Sprint 5.13-B Heuristic: Fast Clique Check"""
import numpy as np
import networkx as nx

def heuristic_check():
    print("Loading candidates...")
    X = np.load("sprint513_candidates.npy")
    N = len(X)
    
    threshold = 0.500001
    G_mat = X @ X.T
    Adj = (G_mat <= threshold)
    np.fill_diagonal(Adj, 0)
    G = nx.from_numpy_array(Adj)
    
    print(f"Graph: {N} nodes, Density: {nx.density(G):.3f}")
    
    print("Running Heuristic (max_weight_clique approx)...")
    # Actually nx.approximation.max_clique is good
    cliques = nx.approximation.clique.max_clique(G)
    print(f"Heuristic Size: {len(cliques)}")
    print(f"Indices: {list(cliques)}")
    
    # Check D5 signature on this result
    from sprint513_clique_solver import d5_signature_score
    cnt = sum(d5_signature_score(X[i]) for i in cliques)
    print(f"D5 hits in heuristic: {cnt}/{len(cliques)}")

if __name__ == "__main__":
    heuristic_check()
