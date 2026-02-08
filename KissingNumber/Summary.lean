import KissingNumber.D3
import KissingNumber.D5
import KissingNumber.Witness.E8
import KissingNumber.K
import KissingNumber.Certificates.LP_K8_240

open KissingNumber

/-!
# Kissing Number Verification Summary

This project formally verifies kissing numbers in specific dimensions
using explicit witness configurations and the Delsarte LP bound.

## Dimensions and Configurations:
- **Dimension 3**: 12 points (Cuboctahedron / D3 Root System)
- **Dimension 5**: 40 points (D5 Lattice Roots)
- **Dimension 8**: 240 points (E8 Lattice Roots)

All configurations are proven to satisfy:
1. `‖X i‖ = 2` (All points on sphere of radius 2)
2. `‖X i - X j‖ ≥ 2` (All points separated by at least 2)

## Formal Bounds on K(n):
- `12 ≤ K(3)` via D3 root system witness
- `40 ≤ K(5)` via D5 root system witness
- `K(8) = 240` via E8 witness (lower bound) + Delsarte LP bound (upper bound)
  - Upper bound: PSD proved for k=1,2,3,4,5 via feature maps; sorry for k=6
-/

/-- The kissing number in dimension 3 is at least 12. -/
theorem verified_tau_3_ge_12 : ∃ X : Fin 12 → EuclideanSpace ℝ (Fin 3),
    IsKissingConfiguration 3 12 X :=
  exists_kissing_12

/-- The kissing number in dimension 5 is at least 40. -/
theorem verified_tau_5_ge_40 : ∃ X : Fin 40 → EuclideanSpace ℝ (Fin 5),
    IsKissingConfiguration 5 40 X :=
  exists_kissing_40

/-- The kissing number in dimension 8 is at least 240. -/
theorem verified_tau_8_ge_240 : ∃ X : Fin 240 → EuclideanSpace ℝ (Fin 8),
    IsKissingConfiguration 8 240 X :=
  exists_kissing_240

/-! ## Formal lower bounds on K(n) as inequalities -/

theorem twelve_le_K3 : (12 : WithTop ℕ) ≤ K 3 :=
  le_K_of_exists exists_kissing_12

theorem forty_le_K5 : (40 : WithTop ℕ) ≤ K 5 :=
  le_K_of_exists exists_kissing_40

theorem two_forty_le_K8 : (240 : WithTop ℕ) ≤ K 8 :=
  le_K_of_exists exists_kissing_240

/-! ## Exact kissing number for dimension 8 -/

/-- The kissing number in dimension 8 is exactly 240.
    Lower bound: E8 root system witness (axiom-free).
    Upper bound: Delsarte LP bound; PSD for k=1,2,3,4,5 proved, k=6 sorry. -/
theorem K8_eq_240_summary : K 8 = 240 := K8_eq_240
