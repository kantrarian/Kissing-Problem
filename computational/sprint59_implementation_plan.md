# Sprint 5.9-B: Max-Min Gap Optimizer

## Problem
Sprint 5.9-A showed clustering at -0.047 and -0.098 gaps. The softplus² objective reduces *total* overlap, not the *worst* pair.

## Solution: Log-Sum-Exp Objective
```
L = τ * log(Σ exp(-gap_ij / τ))
```
Minimizing L ≈ minimizing max overlap ≈ maximizing min gap.

## Falsification Matrix
| N | Expected Outcome |
|---|------------------|
| 40 | Should certify (known feasible) |
| 41 | Target (gap ~0 or hard wall?) |
| 45 | Should fail hard (control) |

## Implementation
- `sprint59b_maxmin_search.py`
- Log-sum-exp objective with gradient
- Two-stage: explore (high τ) → polish (low τ)
- Run N=40, 41, 45 with 50 restarts each
