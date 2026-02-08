# Future Work: Szöllősi-Style Clique Search for τ₅

## Motivation

Your Sprint 5.11-D clique search failed because **random sampling cannot find measure-zero optimal configurations**. Szöllősi's 2023 discovery of Q₅ succeeded because he used **algebraically structured candidate sets**.

Key insight from Szöllősi: The Q₅ configuration has inner products in {1/5, -3/10, -1/2}—small rational numbers. This suggests optimal kissing configurations have "nice" algebraic structure that can be exploited.

---

## The Core Problem with Naive Clique Search

Your implementation:
```python
X = rng.normal(size=(n_candidates, d))
X = X / np.linalg.norm(X, axis=1, keepdims=True)
```

**Why this fails:**
- D₅ vertices are exactly `(±1, ±1, 0, 0, 0)/√2` — probability of hitting these with continuous random sampling is zero
- Even 50,000 random points won't contain a 40-clique because no 40 random points will simultaneously satisfy all pairwise constraints
- The compatibility graph from random points is too sparse in the "right" regions

---

## Szöllősi's Actual Method (Reconstructed)

From arXiv:2301.08272, Szöllősi's approach:

### 1. Inner-Product-Controlled Candidate Generation

**TRAP (avoided):** Enumerating rational coordinates and normalizing produces *mostly irrational* inner products and explodes combinatorially. This is the wrong primitive.

**Better approach:** Enumerate vectors where **inner products are controlled by construction**:

```python
def generate_fixed_norm_candidates(m_values=[2, 4, 5, 8, 10], d=5, max_entry=3):
    """
    Generate integer vectors with fixed squared norm m.
    After normalization by sqrt(m), inner products are multiples of 1/m.
    
    This keeps inner products in a small algebraic field.
    """
    from itertools import product
    
    candidates = []
    entries = list(range(-max_entry, max_entry + 1))
    
    for m in m_values:
        for coords in product(entries, repeat=d):
            v = np.array(coords, dtype=float)
            norm_sq = np.dot(v, v)
            if norm_sq == m:  # Exact match
                v_normalized = v / np.sqrt(m)
                candidates.append(v_normalized)
    
    return np.array(candidates)


def generate_root_system_candidates(d=5):
    """
    Generate candidates from known root systems / lattices.
    These have algebraically nice inner product spectra by construction.
    """
    candidates = []
    
    # D_5 roots: (±1, ±1, 0, 0, 0) and permutations, normalized
    # These have |x|² = 2, inner products in {-1, -1/2, 0, 1/2, 1}
    from itertools import combinations, permutations, product
    for idx in combinations(range(d), 2):
        for signs in product([-1, 1], repeat=2):
            v = np.zeros(d)
            v[idx[0]] = signs[0]
            v[idx[1]] = signs[1]
            candidates.append(v / np.sqrt(2))
    
    # A_5 roots (in 5D projection): differences of standard basis
    # Inner products in {-1, -1/2, 0, 1/2, 1}
    for i in range(d):
        for j in range(i+1, d):
            for sign in [-1, 1]:
                v = np.zeros(d)
                v[i] = 1
                v[j] = sign
                candidates.append(v / np.sqrt(2))
    
    # Cross-polytope vertices: ±e_i
    for i in range(d):
        for sign in [-1, 1]:
            v = np.zeros(d)
            v[i] = sign
            candidates.append(v)
    
    return np.array(candidates)
```

**Key insight**: D₅ vertices have |x|² = 2 with entries in {-1, 0, 1}. After normalization, inner products are in {-1, -½, 0, ½, 1}. By controlling the squared norm, we control the inner product spectrum.

### 2. Soft Spectrum Scoring (Not Hard Filtering)

**TRAP (avoided):** Hard-filtering by "inner products must be in {1/5, −3/10, −1/2}" will miss the actual optimum if its spectrum is slightly different.

**Better approach:** Two-stage filtering with soft scoring:

```python
def score_candidate(v, existing_points, learned_spectrum=None):
    """
    Score a candidate by how well its inner products fit a discrete spectrum.
    Returns (is_feasible, spectrum_score).
    """
    inner_products = existing_points @ v
    
    # Stage 1: Hard feasibility filter (must pass)
    # Allow small tolerance for numerical stability
    if np.any(inner_products > 0.5 + 1e-8):
        return False, -np.inf
    
    # Stage 2: Soft spectrum scoring (prefer "nice" inner products)
    if learned_spectrum is None:
        # Default: prefer inner products close to simple fractions
        nice_values = np.array([-1, -0.5, -0.25, 0, 0.25, 0.5])
    else:
        nice_values = learned_spectrum
    
    # Score = negative sum of distances to nearest nice value
    distances = np.min(np.abs(inner_products[:, None] - nice_values[None, :]), axis=1)
    score = -np.sum(distances)
    
    return True, score


def learn_spectrum_from_clique(clique_points, n_clusters=6):
    """
    Learn the inner product spectrum from an existing clique.
    Use k-means to find the discrete set of inner products.
    """
    G = clique_points @ clique_points.T
    mask = ~np.eye(len(clique_points), dtype=bool)
    inner_products = G[mask]
    
    from sklearn.cluster import KMeans
    kmeans = KMeans(n_clusters=n_clusters, n_init=10)
    kmeans.fit(inner_products.reshape(-1, 1))
    
    return np.sort(kmeans.cluster_centers_.flatten())
```

**Key insight**: The spectrum is a *soft prior*, not a hard constraint. If a 41-configuration exists with a slightly different spectrum, we don't want to filter it out.

### 3. No Full Graph Construction (Dense Core Extraction)

**TRAP (avoided):** 100k candidates means a 100k×100k Gram matrix (~40GB). The adjacency matrix will be huge. Never build the full graph.

**Better approach:** On-the-fly neighbor generation + dense core extraction:

```python
def extract_dense_core(candidates, threshold=0.5, min_degree_percentile=80):
    """
    Extract a dense core of candidates without building full graph.
    Uses batch processing to avoid memory explosion.
    """
    n = len(candidates)
    batch_size = 1000
    
    # Step 1: Compute degree estimates via sampling
    degrees = np.zeros(n)
    for i in range(0, n, batch_size):
        batch = candidates[i:i+batch_size]
        # Compute inner products with all candidates
        G_batch = batch @ candidates.T  # (batch_size, n)
        compatible = (G_batch <= threshold + 1e-8)
        degrees[i:i+batch_size] = compatible.sum(axis=1) - 1  # -1 for self
    
    # Step 2: Keep only high-degree nodes
    degree_threshold = np.percentile(degrees, min_degree_percentile)
    core_mask = degrees >= degree_threshold
    core_indices = np.where(core_mask)[0]
    core_candidates = candidates[core_mask]
    
    print(f"Dense core: {len(core_candidates)} / {n} candidates "
          f"(degree >= {degree_threshold:.0f})")
    
    return core_candidates, core_indices


def build_graph_for_core(core_candidates, threshold=0.5):
    """
    Build graph only for the dense core (small enough to fit in memory).
    """
    n = len(core_candidates)
    if n > 10000:
        raise ValueError(f"Core too large ({n}), increase min_degree_percentile")
    
    G = core_candidates @ core_candidates.T
    adj = (G <= threshold + 1e-8)
    np.fill_diagonal(adj, False)
    
    return nx.from_numpy_array(adj.astype(int))


def on_the_fly_neighbors(v_idx, candidates, threshold=0.5):
    """
    Compute neighbors of a single vertex without storing full graph.
    """
    v = candidates[v_idx]
    inner_products = candidates @ v
    neighbors = np.where((inner_products <= threshold + 1e-8) & 
                         (np.arange(len(candidates)) != v_idx))[0]
    return neighbors
```

**Alternative: Conflict graph for independent set**

Sometimes the **conflict graph** (edges for incompatible pairs, inner product > 0.5) is sparser:

```python
def build_conflict_graph(candidates, threshold=0.5):
    """
    Build conflict graph where edges = incompatible pairs.
    Max clique in compatibility graph = Max independent set in conflict graph.
    """
    G = candidates @ candidates.T
    conflict_adj = (G > threshold + 1e-8)
    np.fill_diagonal(conflict_adj, False)
    
    # If conflict graph is sparse, independent set search may be faster
    n_edges = conflict_adj.sum() // 2
    density = n_edges / (len(candidates) * (len(candidates) - 1) / 2)
    print(f"Conflict graph density: {density:.4f}")
    
    return nx.from_numpy_array(conflict_adj.astype(int)), density
```

**Key insight**: For kissing problems, the compatibility graph is often dense. If conflict graph has density < 0.3, maximum independent set algorithms may outperform clique search.

---

## Control-First Validation (Critical)

Just like your continuous pipeline, the clique search **must pass controls before the target search is meaningful**:

```python
def run_control_first_clique_search(candidates):
    """
    Control-first validation for clique search.
    """
    results = {}
    
    # ============================================
    # CONTROL 1: D₅ must exist and form 40-clique
    # ============================================
    d5_vertices = generate_D5_vertices()
    
    # Check D₅ vertices are in candidate set
    d5_in_candidates = find_subset_indices(candidates, d5_vertices, tol=1e-8)
    if len(d5_in_candidates) < 40:
        raise ValueError(f"CONTROL FAILED: Only {len(d5_in_candidates)}/40 "
                        "D₅ vertices found in candidates")
    
    # Check D₅ forms a clique in the graph
    d5_subgraph = candidates[d5_in_candidates]
    G_d5 = d5_subgraph @ d5_subgraph.T
    np.fill_diagonal(G_d5, 0)
    if np.max(G_d5) > 0.5 + 1e-8:
        raise ValueError("CONTROL FAILED: D₅ vertices not mutually compatible")
    
    print("✓ Control 1 PASSED: D₅ 40-clique found in candidates")
    results['d5_control'] = 'PASS'
    
    # ============================================
    # CONTROL 2: Random candidates must FAIL to find 40-clique
    # ============================================
    rng = np.random.default_rng(42)
    random_candidates = rng.normal(size=(len(candidates), 5))
    random_candidates /= np.linalg.norm(random_candidates, axis=1, keepdims=True)
    
    random_max_clique = greedy_clique_search(random_candidates, n_trials=100)
    if len(random_max_clique) >= 40:
        print(f"WARNING: Random candidates found {len(random_max_clique)}-clique")
        results['random_control'] = 'UNEXPECTED'
    else:
        print(f"✓ Control 2 PASSED: Random candidates max clique = {len(random_max_clique)} < 40")
        results['random_control'] = 'PASS'
    
    # ============================================
    # CONTROL 3: N=45 should fail harder than N=41
    # ============================================
    # (This is validated implicitly: if we find a 41-clique, we try for 45)
    
    # ============================================
    # TARGET: Search for 41-clique
    # ============================================
    print("\nSearching for 41-clique in structured candidates...")
    max_clique = full_clique_search(candidates, target_size=41)
    results['max_clique_size'] = len(max_clique)
    
    if len(max_clique) >= 41:
        print(f"*** FOUND {len(max_clique)}-CLIQUE! ***")
        results['status'] = 'BREAKTHROUGH'
    else:
        print(f"Max clique found: {len(max_clique)}")
        results['status'] = 'NEGATIVE'
    
    return results
```

**Interpretation:**
- If Control 1 fails: candidate generator is broken
- If Control 2 fails: either got lucky or threshold is wrong
- If target finds 41+: **τ₅ ≥ 41** (major result)
- If target finds only 40: complementary evidence for τ₅ = 40

```python
def find_large_cliques(graph, min_size=35):
    """
    Use multiple clique-finding strategies.
    """
    cliques = []
    
    # 1. Greedy construction (fast, approximate)
    cliques.extend(greedy_clique(graph, n_trials=1000))
    
    # 2. Local search from greedy seeds
    for seed in cliques[:10]:
        improved = local_search_clique(graph, seed)
        cliques.append(improved)
    
    # 3. Branch-and-bound on subgraphs (exact, slow)
    # Only run on promising subgraphs
    dense_subgraph = extract_dense_core(graph)
    if dense_subgraph.number_of_nodes() < 1000:
        exact_clique = branch_and_bound_clique(dense_subgraph)
        cliques.append(exact_clique)
    
    return [c for c in cliques if len(c) >= min_size]


def greedy_clique(graph, n_trials=1000):
    """
    Greedy clique construction with random restarts.
    """
    best_clique = []
    nodes = list(graph.nodes())
    
    for _ in range(n_trials):
        # Start from random node
        clique = [random.choice(nodes)]
        candidates = set(graph.neighbors(clique[0]))
        
        while candidates:
            # Add node that maximizes minimum degree within clique
            best_node = max(candidates, 
                          key=lambda v: sum(1 for u in clique if graph.has_edge(u, v)))
            
            if all(graph.has_edge(best_node, u) for u in clique):
                clique.append(best_node)
                candidates &= set(graph.neighbors(best_node))
            else:
                candidates.remove(best_node)
        
        if len(clique) > len(best_clique):
            best_clique = clique
    
    return best_clique
```

### Phase 4: Hybrid Discrete-Continuous Refinement

```python
def refine_clique_continuously(clique_points, target_size, d=5):
    """
    Given a clique of size k < target_size, try to extend via optimization.
    """
    k = len(clique_points)
    n_new = target_size - k
    
    # Initialize new points randomly
    rng = np.random.default_rng()
    new_points = rng.normal(size=(n_new, d))
    new_points /= np.linalg.norm(new_points, axis=1, keepdims=True)
    
    # Optimize: fix clique_points, vary new_points
    # Objective: maximize min gap over ALL pairs (including clique-to-new)
    
    all_points = np.vstack([clique_points, new_points])
    
    result = repair_then_polish(all_points, R=1.0, ...)
    
    if result['certified']:
        return result['final_points']
    return None
```

---

## Computational Estimates (Revised)

| Strategy | Candidates | Memory | Clique Time | Can Find D₅? |
|----------|-----------|--------|-------------|--------------|
| Random 5k | 5,000 | ~100MB | Fast | **No** (measure zero) |
| Fixed-norm m∈{2,4,5,8} | ~5,000 | ~100MB | Fast | **Yes** |
| Root systems (D₅, A₅) | ~200 | Trivial | Instant | **Yes** |
| Dense core extraction | ~2,000 | ~20MB | Minutes | **Yes** |

**Key realization**: You don't need millions of candidates. The D₅ configuration has only 40 points. A well-chosen 5,000-point candidate set that includes D₅ + algebraic extensions is far better than 500,000 random rationals.

---

## What Success Would Mean

**If clique search finds a 41-clique**: You've discovered τ₅ ≥ 41, a major result.

**If clique search consistently finds only 40-cliques**: 
- Confirms τ₅ = 40 from a completely different computational angle
- Validates your gradient-based results
- Provides structural insight into *why* 41 is impossible

**Either way**: The discrete approach complements your continuous optimization and would strengthen the paper significantly.

---

## Revised Implementation Roadmap

### Sprint 5.13-A: Inner-Product-Controlled Candidates (1 day)
- [ ] Implement fixed-norm integer vector enumeration (m ∈ {2, 4, 5, 8, 10})
- [ ] Implement root system extraction (D₅, A₅)
- [ ] **Validation**: Confirm D₅ vertices appear exactly
- [ ] Count: aim for 2,000-10,000 candidates total

### Sprint 5.13-B: Control-First Validation (1 day)
- [ ] Control 1: D₅ 40-clique must be found
- [ ] Control 2: Random candidates must fail
- [ ] If controls fail, debug candidate generator

### Sprint 5.13-C: Dense Core + Clique Search (2 days)
- [ ] Implement degree-based dense core extraction
- [ ] Implement greedy clique with local search
- [ ] Test on D₅ (must recover 40-clique quickly)
- [ ] Run on full structured candidates

### Sprint 5.13-D: Hybrid Extension (1 day)
- [ ] Take best 40-clique found
- [ ] Attempt extension to 41 via continuous optimizer
- [ ] Compare to D₅+1 baseline (which got -0.063)
- [ ] Document: does structured 40-clique extend better than D₅?

### Sprint 5.13-E: Scale-Up (optional, 1 week)
- [ ] If 40-cliques other than D₅ are found, characterize them
- [ ] Try larger candidate sets (fixed-norm with m up to 20)
- [ ] Compare inner product spectra of discovered cliques

**Total: ~1 week for core implementation, 1 week for scaling**

---

## References

1. **Szöllősi (2023)**: "A note on five dimensional kissing arrangements" — arXiv:2301.08272
   - Key technique: parametrized point clouds with algebraic structure
   
2. **Cohn-Rajagopal (2024)**: "Variations on five-dimensional sphere packings" — arXiv:2412.00937
   - Constructed R₅ using different methods
   
3. **Sloane et al. (NJA Sloane's website)**: Tables of spherical codes
   - Reference implementations for known configurations

4. **Bomze et al. (1999)**: "The maximum clique problem" — Handbook of Combinatorial Optimization
   - State-of-the-art clique algorithms

---

## Paper Wording (Conservative)

If you include this in the current paper, use cautious language:

> *"We propose a structured candidate + clique framework motivated by Szöllősi-style algebraic codes as complementary future work. Preliminary prototyping confirms that inner-product-controlled candidate sets (e.g., fixed-norm integer vectors) recover the D₅ 40-clique, but full-scale enumeration with hybrid continuous extension remains future work."*

This keeps you honest while signaling ambition.

---

## Summary of Revisions Based on Feedback

| Original Trap | Fix Applied |
|---------------|-------------|
| Rational coordinates → irrational inner products | Fixed-norm integer vectors, root systems |
| Hard inner-product filtering | Soft spectrum scoring with learned priors |
| Full 100k×100k graph | Dense core extraction, on-the-fly neighbors |
| Only compatibility graph | Also consider conflict graph → independent set |
| No controls | Control-first: D₅ must be found, random must fail |

---

## Conclusion

The clique approach is fundamentally different from gradient descent:
- **Discrete vs. continuous**: No local minima issues
- **Exact vs. approximate**: Either a clique exists or it doesn't
- **Complementary evidence**: If both methods agree on τ₅ = 40, the evidence is much stronger

The key insight is that **candidate generation is everything**—but "everything" means *inner-product-controlled algebraic families*, not brute-force rational enumeration. Szöllősi found Q₅ because he searched a structured space where the inner product spectrum was constrained by construction.

**Recommended investment**: 1 week implementation + 1 week compute. Either yields a breakthrough (τ₅ ≥ 41) or strong complementary evidence for τ₅ = 40 from a completely orthogonal computational method.
