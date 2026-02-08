# Sprint 5.18: Reproducibility & Sensitivity Freeze Report

**Generated:** 2026-01-29 04:50:58 (aggregated)

## Configuration

- Dimensions: [2, 8]
- Modes: ['Random', 'Rotated']
- Noise scales (Rotated): [0.05, 0.1, 0.2]
- Trials: 10
- Budget (restarts/trial): 20
- Tolerances: eps_g = 1e-06, eps_r = 1e-06
- Base seed: 518

---

## Cross-Dimension Summary

One row per dimension, showing Rotated (noise=0.10) and Random results.

*Note: Some dimensions were run with fewer trials due to compute constraints.*

| Dim | tau | Symmetry | Mode | tau Success | tau Gap | tau+1 Success | tau+1 Gap | Separation |
|-----|-----|----------|------|-------------|---------|---------------|-----------|------------|
| 2 | 6 | Hexagon | Rotated | 100% | -0.000000 | 0% | -0.264465 | 0.264465 |
| 2 | 6 | Hexagon | Random | 100% | -0.000000 | 0% | -0.264465 | 0.264465 |
| 8 | 240 | E8 Lattice | Rotated | 100% | -0.000001 | 0% | -0.130265 | 0.130264 |
| 8 | 240 | E8 Lattice | Random | 0% | -0.000010 | 0% | -0.130274 | 0.130264 |

---

## Dimension 2 (tau=6, Hexagon)

### Results Table

| N | Mode | Noise | Success Rate (95% CI) | Median Gap | Min Gap | Basin Entry |
|---|------|-------|----------------------|------------|---------|-------------|
| 6 | Random | 0.00 | 100.0% [72.2%-100.0%] | -0.000000 | -0.000000 | 100.0% |
| 6 | Rotated | 0.05 | 100.0% [72.2%-100.0%] | -0.000000 | -0.000001 | 100.0% |
| 6 | Rotated | 0.10 | 100.0% [72.2%-100.0%] | -0.000000 | -0.000000 | 100.0% |
| 6 | Rotated | 0.20 | 100.0% [72.2%-100.0%] | -0.000000 | -0.000000 | 100.0% |
| 7 | Random | 0.00 | 0.0% [0.0%-27.8%] | -0.264465 | -0.264465 | 0.0% |
| 7 | Rotated | 0.05 | 0.0% [0.0%-27.8%] | -0.264465 | -0.264465 | 0.0% |
| 7 | Rotated | 0.10 | 0.0% [0.0%-27.8%] | -0.264465 | -0.264465 | 0.0% |
| 7 | Rotated | 0.20 | 0.0% [0.0%-27.8%] | -0.264465 | -0.264465 | 0.0% |

### Separation Analysis (tau vs tau+1)

| Mode | Noise | Median Gap @ tau | Median Gap @ tau+1 | Separation |
|------|-------|------------------|--------------------| -----------|
| Random | 0.00 | -0.000000 | -0.264465 | 0.264465 |
| Rotated | 0.05 | -0.000000 | -0.264465 | 0.264465 |
| Rotated | 0.10 | -0.000000 | -0.264465 | 0.264465 |
| Rotated | 0.20 | -0.000000 | -0.264465 | 0.264465 |

## Dimension 8 (tau=240, E8 Lattice)

### Results Table

| N | Mode | Noise | Success Rate (95% CI) | Median Gap | Min Gap | Basin Entry |
|---|------|-------|----------------------|------------|---------|-------------|
| 240 | Random | 0.00 | 0.0% [0.0%-56.2%] | -0.000010 | -0.000018 | 90.0% |
| 240 | Rotated | 0.05 | 100.0% [43.8%-100.0%] | -0.000001 | -0.000001 | 100.0% |
| 240 | Rotated | 0.10 | 100.0% [43.8%-100.0%] | -0.000001 | -0.000001 | 100.0% |
| 240 | Rotated | 0.20 | 100.0% [43.8%-100.0%] | -0.000001 | -0.000001 | 100.0% |
| 241 | Random | 0.00 | 0.0% [0.0%-56.2%] | -0.130274 | -0.130274 | 0.0% |
| 241 | Rotated | 0.05 | 0.0% [0.0%-56.2%] | -0.130268 | -0.130275 | 0.0% |
| 241 | Rotated | 0.10 | 0.0% [0.0%-56.2%] | -0.130265 | -0.130274 | 0.0% |
| 241 | Rotated | 0.20 | 0.0% [0.0%-56.2%] | -0.130267 | -0.130276 | 0.0% |

### Separation Analysis (tau vs tau+1)

| Mode | Noise | Median Gap @ tau | Median Gap @ tau+1 | Separation |
|------|-------|------------------|--------------------| -----------|
| Random | 0.00 | -0.000010 | -0.130274 | 0.130264 |
| Rotated | 0.05 | -0.000001 | -0.130268 | 0.130267 |
| Rotated | 0.10 | -0.000001 | -0.130265 | 0.130264 |
| Rotated | 0.20 | -0.000001 | -0.130267 | 0.130266 |

---

## Interpretation

### Evidence Strength

The results above provide **strong computational evidence** supporting the following observations:

1. **At N=tau**: The optimizer consistently finds configurations with gaps near zero or positive,
   indicating that packing tau unit spheres on a sphere of radius 2 is computationally feasible.

2. **At N=tau+1**: The optimizer fails to achieve positive gaps, with median gaps significantly
   below zero. This provides computational evidence that tau+1 spheres cannot fit.

3. **Separation**: The gap between tau and tau+1 median gaps quantifies the computational
   'margin' distinguishing feasible from infeasible configurations.

### Important Caveats

**This is NOT a mathematical proof.** The evidence is subject to:

- **Optimizer dependence**: Results depend on the specific optimization algorithm (annealed Adam),
  hyperparameters, and seeding strategy. A different optimizer might find better configurations.

- **Finite restarts**: With budget=20 restarts per trial, we cannot
  exhaustively search the configuration space. Rare successful configurations might be missed.

- **Numerical tolerances**: Certification uses eps_g=1e-06,
  eps_r=1e-06. Configurations very close to the boundary
  may be misclassified due to floating-point limitations.

- **Seed sensitivity**: Results may vary with different base seeds, though deterministic
  seeding ensures reproducibility for a given seed.

The computational experiments support the conjecture but do not constitute a rigorous proof.

---

*Report generated by sprint518_repro_sensitivity.py*