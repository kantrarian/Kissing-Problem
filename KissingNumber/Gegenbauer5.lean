import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Gegenbauer Polynomials for Dimension 5

Normalized Gegenbauer (ultraspherical) polynomials P₀,...,P₅ for parameter λ=3/2 (dimension d=5),
normalized so that P_k(1) = 1.

These are used in the Delsarte linear programming bound for kissing numbers.

## Recurrence (ultraspherical C_k^{3/2}):
  C₀ = 1,  C₁ = 3t
  (k+1) C_{k+1} = 2(k + 3/2) t C_k - (k+2) C_{k-1}

Normalized: P_k(t) = C_k(t) / C_k(1)
-/

open scoped BigOperators

/-- Normalized Gegenbauer polynomials for d=5 (λ=3/2), P_k(1) = 1 for each k. -/
noncomputable def P5 : Fin 6 → ℝ → ℝ
  | ⟨0, _⟩, _ => 1
  | ⟨1, _⟩, t => t
  | ⟨2, _⟩, t => (5 * t ^ 2 - 1) / 4
  | ⟨3, _⟩, t => (7 * t ^ 3 - 3 * t) / 4
  | ⟨4, _⟩, t => (21 * t ^ 4 - 14 * t ^ 2 + 1) / 8
  | ⟨5, _⟩, t => (33 * t ^ 5 - 30 * t ^ 3 + 5 * t) / 8

@[simp] lemma P5_0 (t : ℝ) : P5 0 t = 1 := rfl
@[simp] lemma P5_1 (t : ℝ) : P5 1 t = t := rfl
@[simp] lemma P5_2 (t : ℝ) : P5 2 t = (5 * t ^ 2 - 1) / 4 := rfl
@[simp] lemma P5_3 (t : ℝ) : P5 3 t = (7 * t ^ 3 - 3 * t) / 4 := rfl
@[simp] lemma P5_4 (t : ℝ) : P5 4 t = (21 * t ^ 4 - 14 * t ^ 2 + 1) / 8 := rfl
@[simp] lemma P5_5 (t : ℝ) : P5 5 t = (33 * t ^ 5 - 30 * t ^ 3 + 5 * t) / 8 := rfl

/-- Each normalized Gegenbauer polynomial evaluates to 1 at t=1. -/
theorem P5_eval_one (k : Fin 6) : P5 k 1 = 1 := by
  fin_cases k <;> simp [P5] <;> norm_num
