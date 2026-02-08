# Sprint 5.14: Potential Closed-Form for the N=41 Gap

## Empirical Result
Our optimization finds:
* **Best gap**: −0.0364 (from 200 restarts)
* **Median gap**: −0.0367

## Candidate Closed Forms

### Formula 1: Kissing-number scaling
$$g_d = -\frac{\pi}{\tau_d \cdot \binom{d}{2}^{1/3}}$$
* For d=5: $g_5 = -\frac{\pi}{40 \cdot 10^{1/3}} = -0.03645...$
* **Error**: 0.15% (vs -0.0364)
* Components: $\tau_5 = 40$ (Kissing Number), $C(5,2) = 10$ (Coord pairs).

### Formula 2: Angular offset
$$g_d = \cos\left(2 - \frac{\pi}{2(d-1)}\right)$$
* For d=5: $g_5 = \cos(2 - \pi/8) = -0.03650...$
* **Error**: 0.27%
* Components: Dimension-dependent angular offset.

### Formula 3: $\pi^2$ scaling
$$g_5 = -\frac{\pi^2}{270} = -0.03655...$$
* **Error**: 0.42%

## Generalization Predictions (Formula 1)
If Formula 1 holds, predicted gaps for other dimensions (N = $\tau_d + 1$):

| d | $\tau_d$ | $C(d,2)$ | Predicted gap |
|---|----------|----------|---------------|
| 3 | 12 | 3 | −0.1815 |
| 4 | 24 | 6 | **−0.0720** |
| 5 | 40 | 10 | **−0.0365** |
| 6 | 72 | 15 | −0.0177 |
| 7 | 126 | 21 | −0.0090 |
| 8 | 240 | 28 | −0.0043 |

## Implementation Plan
1.  **High-Precision Refinement**: Run `repair_then_polish` on N=41, d=5 with `ftol=1e-12` to stabilize the standard gap to 4-5 sig figs.
2.  **Dimension 4 Control**: Run N=25 (known impossible) in d=4. Compare empirical gap to -0.0720.
## Results (Sprint 5.14)

### High-Precision Refinement (d=5, N=41)
* **Starting Gap**: -0.036465
* **Final Refined Gap**: **-0.036723** ($10^{-10}$ precision polish)
* **Conclusion**: The "softer" -0.0364 result was likely an artifact of the smooth `tau` parameter. As `tau \to 0`, the gap widens slightly to -0.0367.

### Hypothesis Check
| Formula | Prediction | Empirical (-0.03672) | Error |
|---------|------------|----------------------|-------|
| F1 (Kissing) | -0.03645 | -0.03672 | 0.00027 (0.7%) |
| F2 (Angle) | -0.03650 | -0.03672 | 0.00022 (0.6%) |
| F3 ($\pi^2$) | -0.03655 | -0.03672 | 0.00017 (0.5%) |

### Dimension 4 Control (N=25)
* **Predicted (F1)**: -0.0720
* **Empirical**: **-0.0825**
* **Error**: 14.6%

### Final Verdict
None of the proposed simple closed-form expressions are exact.
* Formula 3 ($-\pi^2/270$) is the closest for d=5, but no formula consistently predicts d=4.
* The obstruction constant is likely complex/transcendental and specific to the geometry of the D5 holes.

