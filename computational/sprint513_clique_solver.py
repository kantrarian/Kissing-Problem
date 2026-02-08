"""Sprint 5.13-B: Exact max clique on structured candidate set (with verification)"""

import sys
import time
import numpy as np
import networkx as nx

def min_distance_gap_from_maxcos(max_cos: float) -> float:
    # unit vectors v_i on S^4, points on kissing sphere are x_i = 2 v_i
    # distance = ||2v_i - 2v_j|| = 2*sqrt(2 - 2 cos)
    return 2.0 * np.sqrt(2.0 - 2.0 * max_cos) - 2.0

def verify_clique(X: np.ndarray, idx: np.ndarray, verify_tol: float = 1e-12):
    C = X[idx]
    # Ensure unit norm (defensive)
    norms = np.linalg.norm(C, axis=1)
    norm_err = np.max(np.abs(norms - 1.0))

    G = C @ C.T
    np.fill_diagonal(G, -1.0)  # ignore diagonal
    max_cos = float(np.max(G))
    ok = (max_cos <= 0.5 + verify_tol)

    return {
        "ok": ok,
        "max_cos": max_cos,
        "g_min_distance": float(min_distance_gap_from_maxcos(max_cos)),
        "max_norm_err": float(norm_err),
    }

def d5_signature_score(v: np.ndarray, atol: float = 2e-8) -> bool:
    """
    D5 roots (unit vectors) look like: exactly two coords are ±1/sqrt(2), rest 0
    (up to sign/permutation). This is a cheap sanity check.
    """
    a = 1.0 / np.sqrt(2.0)
    nz = np.where(np.abs(v) > atol)[0]
    if len(nz) != 2:
        return False
    return (np.allclose(np.abs(v[nz]), a, atol=5e-7) and
            np.all(np.abs(np.delete(v, nz)) < atol))

def solve_clique_problem(
    candidates_path="sprint513_candidates.npy",
    build_tol=1e-6,
    verify_tol=1e-12,
):
    sys.setrecursionlimit(20000)  # max_weight_clique is recursive

    print("Loading candidates...")
    X = np.load(candidates_path).astype(np.float64, copy=False)
    N, d = X.shape
    print(f"Loaded {N} candidates in {d}D.")

    # Defensive renormalization (prevents subtle drift)
    X /= np.linalg.norm(X, axis=1, keepdims=True)

    threshold = 0.5 + build_tol
    print(f"Building compatibility graph with build_tol={build_tol} (threshold={threshold})...")

    t0 = time.time()
    Gm = X @ X.T
    # numerical safety
    np.clip(Gm, -1.0, 1.0, out=Gm)

    Adj = (Gm <= threshold)
    np.fill_diagonal(Adj, False)

    # Build edges from upper triangle only (avoids redundant work)
    iu, ju = np.where(np.triu(Adj, 1))
    G = nx.Graph()
    G.add_nodes_from(range(N))
    G.add_edges_from(zip(iu.tolist(), ju.tolist()))

    print(f"Graph built in {time.time() - t0:.2f}s.")
    print(f"Nodes: {G.number_of_nodes()}, Edges: {G.number_of_edges()}, Density: {nx.density(G):.3f}")

    print("Finding Maximum Clique (exact branch-and-bound)...")
    t1 = time.time()
    clique_nodes, clique_weight = nx.algorithms.clique.max_weight_clique(G, weight=None)  # exact
    clique_nodes = np.array(clique_nodes, dtype=int)
    print(f"Done in {time.time() - t1:.2f}s.")
    print(f"*** Max Clique Size: {len(clique_nodes)} ***")

    # Verify geometrically with strict tol
    ver = verify_clique(X, clique_nodes, verify_tol=verify_tol)
    print("Verification (strict):", ver)

    # Optional: D5 containment heuristic
    d5_hits = sum(d5_signature_score(X[i]) for i in clique_nodes)
    print(f"D5-signature hits inside clique: {d5_hits}/{len(clique_nodes)}")

    np.save("sprint513_max_clique_indices.npy", clique_nodes)
    np.save("sprint513_max_clique_points.npy", X[clique_nodes])

    # If you ever get 41+, immediately re-run verification at tighter tolerances
    # and compute the exact worst-pair dot list.
    if len(clique_nodes) >= 41:
        print("!!! Potential breakthrough: clique size >= 41. Re-checking with tighter verify_tol=1e-14 ...")
        print(verify_clique(X, clique_nodes, verify_tol=1e-14))

if __name__ == "__main__":
    solve_clique_problem()
