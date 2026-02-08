import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

open scoped BigOperators
open Real

abbrev R5 : Type := EuclideanSpace ℝ (Fin 5)

-- A D5 index is a pair of distinct coordinates (p.1 < p.2) and two signs
abbrev Pair5 := {p : Fin 5 × Fin 5 // p.1 < p.2}
abbrev Sign2 := Bool × Bool
abbrev D5Index := Pair5 × Sign2

noncomputable def sgn (b : Bool) : ℝ := if b then (1:ℝ) else (-1)

-- Definition of the 40 vectors of the D5 root system (scaled to norm 2)
-- Each vector has exactly two non-zero coordinates with value ±√2.
noncomputable def d5Vec (idx : D5Index) : R5 :=
  let i := idx.1.1.1
  let j := idx.1.1.2
  let si := sgn idx.2.1
  let sj := sgn idx.2.2
  fun k =>
    if k = i then si * Real.sqrt 2
    else if k = j then sj * Real.sqrt 2
    else 0

-- Helper lemma: sgn squared is 1
lemma sgn_sq (b : Bool) : (sgn b)^2 = (1:ℝ) := by
  by_cases hb : b <;> simp [sgn, hb]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = (1:ℝ) := by
  by_cases hb : b <;> simp [sgn, hb]

-- Lemma 1: All vectors have norm 2
lemma norm_d5Vec (idx : D5Index) : ‖d5Vec idx‖ = 2 := by
  sorry

-- Accessors for coordinates
noncomputable def iCoord (idx : D5Index) : Fin 5 := idx.1.1.1
noncomputable def jCoord (idx : D5Index) : Fin 5 := idx.1.1.2

-- Lemma 2: Inner product is at most 2 for distinct vectors
lemma inner_d5Vec_le_two (a b : D5Index) (hab : a ≠ b) :
    ⟪d5Vec a, d5Vec b⟫_ℝ ≤ 2 := by
  sorry

-- Lemma 3: Pairwise distance is at least 2
lemma dist_d5Vec_ge_two (a b : D5Index) (hab : a ≠ b) :
    ‖d5Vec a - d5Vec b‖ ≥ 2 := by
  sorry
