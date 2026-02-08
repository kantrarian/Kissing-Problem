import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Gegenbauer Polynomials for Dimension 8

Normalized Gegenbauer (ultraspherical) polynomials P₀,...,P₆ for parameter λ=3 (dimension n=8),
normalized so that P_k(1) = 1.

These are used in the Delsarte linear programming bound for kissing numbers.
-/

open scoped BigOperators

/-- Normalized Gegenbauer polynomials for n=8 (λ=3), P_k(1) = 1 for each k. -/
noncomputable def P8 : Fin 7 → ℝ → ℝ
  | ⟨0, _⟩, _ => 1
  | ⟨1, _⟩, t => t
  | ⟨2, _⟩, t => (8 * t ^ 2 - 1) / 7
  | ⟨3, _⟩, t => (10 * t ^ 3 - 3 * t) / 7
  | ⟨4, _⟩, t => (40 * t ^ 4 - 20 * t ^ 2 + 1) / 21
  | ⟨5, _⟩, t => (56 * t ^ 5 - 40 * t ^ 3 + 5 * t) / 21
  | ⟨6, _⟩, t => (896 * t ^ 6 - 840 * t ^ 4 + 180 * t ^ 2 - 5) / 231

@[simp] lemma P8_0 (t : ℝ) : P8 0 t = 1 := rfl
@[simp] lemma P8_1 (t : ℝ) : P8 1 t = t := rfl
@[simp] lemma P8_2 (t : ℝ) : P8 2 t = (8 * t ^ 2 - 1) / 7 := rfl
@[simp] lemma P8_3 (t : ℝ) : P8 3 t = (10 * t ^ 3 - 3 * t) / 7 := rfl
@[simp] lemma P8_4 (t : ℝ) : P8 4 t = (40 * t ^ 4 - 20 * t ^ 2 + 1) / 21 := rfl
@[simp] lemma P8_5 (t : ℝ) : P8 5 t = (56 * t ^ 5 - 40 * t ^ 3 + 5 * t) / 21 := rfl
@[simp] lemma P8_6 (t : ℝ) : P8 6 t = (896 * t ^ 6 - 840 * t ^ 4 + 180 * t ^ 2 - 5) / 231 := rfl

/-- Each normalized Gegenbauer polynomial evaluates to 1 at t=1. -/
theorem P8_eval_one (k : Fin 7) : P8 k 1 = 1 := by
  fin_cases k <;> simp [P8] <;> norm_num
