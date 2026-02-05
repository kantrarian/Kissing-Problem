import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

open scoped BigOperators RealInnerProductSpace
open Real

/-- 
IsKissingConfiguration d N X
d: Dimension (EuclideanSpace ℝ (Fin d))
N: Number of points
X: The map from Fin N to points
-/
def IsKissingConfiguration (d N : ℕ) (X : Fin N → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i, ‖X i‖ = 2) ∧ (∀ i j, i ≠ j → ‖X i - X j‖ ≥ 2)
