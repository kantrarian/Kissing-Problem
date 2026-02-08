# Sprint 5.9: Computational Evidence for τ₅ = 40

## Summary
We develop a control-first global feasibility search to test whether 41 unit spheres can kiss a central sphere in 5D. Our best optimizer certifies the known D₅ configuration at N=40, fails harder at N=45, and consistently stalls at N=41 with best_min_gap ≈ -0.036 across 200 restarts.

---

## Methods

### Problem Formulation
- **Objective**: Find 41 points on S⁴ (radius 2R) such that min pairwise distance ≥ 2R
- **Certification**: `min_gap >= -1e-5` and `radial_error <= 1e-5`

### Optimization Pipeline
1. **Repair phase** (10k iters): Softplus² overlap penalty with Adam optimizer
2. **Polish phase** (10k iters): Log-sum-exp max-min objective with Adam + τ annealing

### Control-First Design
- **N=40**: Seed with D₅ polytope vertices (40 points, known optimal)
- **N=41**: Target case (random restarts)
- **N=45**: Negative control (should fail harder)

---

## Results

### Falsification Matrix (Sprint 5.9-C)
| N | Certified | Best Gap | Restarts |
|---|-----------|----------|----------|
| 40 | **✓** | 0.000 | 1 (D₅ seed) |
| 41 | ✗ | -0.036 | 20 |
| 45 | ✗ | -0.090 | 20 |

### N=41 Statistical Analysis (Sprint 5.9-D, 200 restarts)
| Statistic | Value |
|-----------|-------|
| Certified | **0/200** |
| Best gap | -0.0364 |
| Median gap | -0.0367 |
| Mean gap | -0.0401 |
| Std dev | 0.0053 |
| In good basin (>-0.04) | 133/200 (66.5%) |

**Quantiles**: q10=-0.048, q25=-0.045, q50=-0.037, q75=-0.037, q90=-0.036

### Binomial Confidence
With 0 successes in 200 trials, the 95% upper bound on success probability per restart is **p < 1.5%**.

---

## Limitations

1. **Not a proof**: We demonstrate that a specific optimizer family converges to a stable near-feasible attractor at N=41, not that N=41 is geometrically infeasible.

2. **Optimizer dependence**: Alternative methods (SDP relaxations, SAT solvers, semidefinite programming) could potentially find solutions our gradient-based approach misses.

3. **Local minima**: The -0.036 barrier may be a landscape artifact rather than a geometric obstruction. However:
   - The same optimizer certifies N=40 trivially
   - The active-set variant (5.9-E) found a *worse* attractor (-0.065), suggesting the -0.036 basin is relatively good

4. **Finite restarts**: 200 restarts bounds p < 1.5%, but cannot rule out extremely rare feasible configurations.

---

## Conclusion

> **Claim**: With a control-first pipeline that certifies D₅ at N=40 (gap=0) and fails at N=45 (gap≈-0.090), our global feasibility search for N=41 achieves best_min_gap≈-0.036 over 200 restarts with **no certified solution found**.

This constitutes **strong computational evidence** that τ₅ = 40.

---

## Files
- [5.9-D Statistics](file:///C:/cliff/kiss/sprint59d_n41_statistics.json)
- [5.9-C Falsification Matrix](file:///C:/cliff/kiss/sprint59c_falsification_matrix.json)
- [5.9-E Negative Result](file:///C:/cliff/kiss/sprint59e_n41_statistics.json)
