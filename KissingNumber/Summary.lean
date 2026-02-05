import KissingNumber.D3
import KissingNumber.D5
import KissingNumber.Witness.E8

/--
# Kissing Number Verification Summary

This project formally verifies the lower bounds for kissing numbers in specific dimensions
using explicit witness configurations.

## Dimensions and Configurations:
- **Dimension 3**: 12 points (Cuboctahedron / D3 Root System)
- **Dimension 5**: 40 points (D5 Lattice Roots)
- **Dimension 8**: 240 points (E8 Lattice Roots)

All configurations are proven to satisfy:
1. `‖X i‖ = 2` (All points on sphere of radius 2)
2. `‖X i - X j‖ ≥ 2` (All points separated by at least 2)
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
