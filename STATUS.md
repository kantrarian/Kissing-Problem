# KissingNumber Project — Status Report

## Overview

This Lean 4 project formally verifies kissing numbers in dimensions 3, 5, and 8 using Mathlib4. The goal is to prove `K(8) = 240` (the exact kissing number in dimension 8) with no `sorry` remaining.

---

## Dimensions at a Glance

| Dimension | Result | Status | Sorry Count |
|-----------|--------|--------|-------------|
| 3 | K(3) >= 12 | **COMPLETE** | 0 |
| 5 | K(5) >= 40 | **COMPLETE** | 0 |
| 8 (lower) | K(8) >= 240 | **COMPLETE** | 0 |
| 8 (upper) | K(8) <= 240 | **IN PROGRESS** | 1 (in PSD.lean k=6) |
| 8 (exact) | K(8) = 240 | **IN PROGRESS** | depends on upper bound |

---

## Dimension 3: K(3) >= 12 — COMPLETE

**Strategy**: Explicit witness — 12 points of the cuboctahedron (D3 root system).

**Files**:
- `Defs.lean` — Defines `IsKissingConfiguration d N X`
- `Lemmas.lean` — Shared lemmas (sparse sums, distance from inner product)
- `D3.lean` — D3 root system witness, norm/distance proofs
  - Proves `exists_kissing_12 : exists X : Fin 12 -> EuclideanSpace R (Fin 3), IsKissingConfiguration 3 12 X`

**Dependencies**: `D3.lean` -> `Defs.lean`, `Lemmas.lean`

**Status**: Fully axiom-free. No sorry's.

---

## Dimension 5: K(5) >= 40 — COMPLETE

**Strategy**: Explicit witness — 40 points of the D5 lattice roots.

**Files**:
- `D5.lean` — D5 root system witness, norm/distance proofs
  - Proves `exists_kissing_40 : exists X : Fin 40 -> EuclideanSpace R (Fin 5), IsKissingConfiguration 5 40 X`

**Dependencies**: `D5.lean` -> `Defs.lean`, `Lemmas.lean`

**Status**: Fully axiom-free. No sorry's.

---

## Dimension 8: K(8) = 240 — IN PROGRESS

This is the main goal. It combines a lower bound (E8 witness) and an upper bound (Delsarte LP).

### Lower Bound: K(8) >= 240 — COMPLETE

**Strategy**: Explicit witness — 240 points of the E8 root system.

**Files**:
- `Witness/E8.lean` — E8 root system witness
  - Uses computable helpers (`parityBit`, `extBit`, `sgnMatchSum`) + `native_decide`
  - Proves `exists_kissing_240`

**Dependencies**: `Witness/E8.lean` -> `Defs.lean`, `Lemmas.lean`

**Status**: Fully axiom-free (uses only `Lean.ofReduceBool` for `native_decide`). No sorry's.

### Upper Bound: K(8) <= 240 — IN PROGRESS

**Strategy**: Delsarte linear programming bound. The certificate polynomial
```
g(t) = (t+1)(t+1/2)^2 * t^2 * (t-1/2)
```
has Gegenbauer expansion g = sum_{k=0}^{6} c_k * P_k with all c_k > 0, g(t) <= 0 on [-1, 1/2], and g(1)/c_0 = 240.

The proof chain:
1. `Gegenbauer.lean` — P8 k t: normalized Gegenbauer polynomials for n=8 — **COMPLETE**
2. `Delsarte.lean` — The abstract Delsarte bound theorem — **COMPLETE**
3. `Certificates/LP_K8_240.lean` — Certificate verification + K8_le_240 — **COMPLETE** (modulo PSD)
4. `PSD.lean` — Positive semidefiniteness: for k=1,...,6 — **1 sorry remaining (k=6)**

### PSD Proof Status by Degree k

The Delsarte bound requires: for all unit vectors u_1,...,u_N on S^7,
```
forall k in {1,...,6}, 0 <= sum_i sum_j P_k(<u_i, u_j>)
```

This is proved via **feature map kernel identities**: if phi_k(x,p) is a feature map with
```
sum_p phi_k(x,p) * phi_k(y,p) = c_k * P_k(<x,y>)
```
then the PSD condition follows because the double sum equals c_k^{-1} * sum_p (sum_i phi_k(u_i,p))^2 >= 0.

| k | Feature Map | Kernel Constant | Status | File |
|---|-------------|-----------------|--------|------|
| 1 | inner product (direct) | 1 | **PROVED** | PSD.lean |
| 2 | phi2 (trace-free 2-tensor) | 7/8 | **PROVED** | PSD.lean |
| 3 | phi3 (trace-free 3-tensor) | 7/10 | **PROVED** | PSD.lean |
| 4 | phi4 (trace-free 4-tensor) | 21/40 | **PROVED** | PSD4CrossTerms.lean |
| 5 | phi5 (trace-free 5-tensor) | 3/8 | **PROVED** | PSD5CrossTerms.lean |
| 6 | phi6 (trace-free 6-tensor) | 231/896 | **IN PROGRESS** | PSD6CrossTerms.lean |

### k=6 Cross-Term Status (PSD6CrossTerms.lean)

The phi6 feature map decomposes as:
```
phi6 = A6 - (1/16)*B6 + (1/224)*C6 - (1/2688)*D6
```

The kernel identity sum_p phi6(x,p)*phi6(y,p) = (231/896)*P_6(s) requires proving 10 cross-term sums
(the other 6 follow by symmetry: sum_IJ(x,y) = sum_JI(y,x)).

| Cross-Term | Value | # Terms | Status |
|------------|-------|---------|--------|
| sum_AA | s^6 | 1 | **PROVED** |
| sum_AB | 15*s^4 | 15 | **PROVED** |
| sum_AC | 45*s^2 | 45 | Delta collapse done, rearrangement needed |
| sum_AD | 15 | 15 | **PROVED** |
| sum_BB | 240*s^4 + 90*s^2 | 225 | sorry |
| sum_BC | 1260*s^2 + 45 | 675 | sorry |
| sum_BD | 540 | 225 | sorry (test file in progress) |
| sum_CC | 7560*s^2 + 1080 | 2025 | sorry |
| sum_CD | 5400 | 675 | sorry |
| sum_DD | 14400 | 225 | **PROVED** |

Where s = <x,y> (inner product).

### End Goal

Eliminate the single `sorry` at PSD.lean line 261 (k=6 case) by completing PSD6CrossTerms.lean.
Once done:
- `#print axioms K8_eq_240` will show only `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` — no `sorryAx`.
- The theorem `K 8 = 240` is fully verified.

---

## File Dependency Graph

```
Summary.lean
  |-- D3.lean -----------------> Defs.lean, Lemmas.lean
  |-- D5.lean -----------------> Defs.lean, Lemmas.lean
  |-- Witness/E8.lean ---------> Defs.lean, Lemmas.lean
  |-- K.lean ------------------> Defs.lean
  |-- Certificates/LP_K8_240.lean
        |-- Delsarte.lean -----> Gegenbauer.lean
        |-- K.lean
        |-- Witness/E8.lean
        |-- PSD.lean
              |-- Gegenbauer.lean
              |-- PSD4CrossTerms.lean -> Gegenbauer.lean
              |-- PSD5CrossTerms.lean -> Gegenbauer.lean
              |-- PSD6CrossTerms.lean -> Gegenbauer.lean  [IN PROGRESS]
```

## File Descriptions

### Core Infrastructure
| File | Purpose |
|------|---------|
| `Defs.lean` | `IsKissingConfiguration d N X`: all points norm 2, pairwise distance >= 2 |
| `Lemmas.lean` | Shared lemmas: sparse sums, inner product to distance bridge |
| `K.lean` | `K n`: kissing number as supremum; `le_K_of_exists` for lower bounds |
| `Gegenbauer.lean` | `P8 k t`: Gegenbauer polynomials P_0,...,P_6 for dimension 8 |
| `Delsarte.lean` | `delsarte_bound_8`: if certificate + PSD, then N <= bound |

### Witnesses (Lower Bounds)
| File | Purpose |
|------|---------|
| `D3.lean` | 12-point cuboctahedron witness for K(3) >= 12 |
| `D5.lean` | 40-point D5 root system witness for K(5) >= 40 |
| `Witness/E8.lean` | 240-point E8 root system witness for K(8) >= 240 |

### PSD Proofs (Upper Bound Chain)
| File | Purpose |
|------|---------|
| `PSD.lean` | Main `P8_sum_nonneg`: dispatches to k=1,...,6 feature maps |
| `PSD4CrossTerms.lean` | k=4 feature map kernel identity (9 cross-terms, all proved) |
| `PSD5CrossTerms.lean` | k=5 feature map kernel identity (all proved) |
| `PSD6CrossTerms.lean` | k=6 feature map kernel identity (4/10 proved, 6 remaining) |

### Certificate
| File | Purpose |
|------|---------|
| `Certificates/LP_K8_240.lean` | E8 certificate g(t), Gegenbauer expansion, K8_le_240, K8_eq_240 |

### Summary
| File | Purpose |
|------|---------|
| `Summary.lean` | Top-level exports: all K(n) theorems |

### Test Files (not part of build)
| File | Purpose |
|------|---------|
| `TestDD.lean` | Prototype for D6*D6 delta collapse |
| `TestCC.lean` | Prototype for C6*C6 approach |
| `TestAC.lean` | Goal state inspection for A6*C6 |
| `TestBD.lean` | Prototype for B6*D6 delta collapse |
| `Test6.lean` | Multi-round delta collapse experiments |
