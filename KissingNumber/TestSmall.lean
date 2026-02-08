import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

private lemma sum_ite_prop_zero8 {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

-- OVERLAP: pair_x = {a,b}, pair_y = {a,c}
set_option maxHeartbeats 4000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
      (if a = b then (1:ℝ) else 0) * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f *
      ((if a = c then (1:ℝ) else 0) * y.ofLp b * y.ofLp d * y.ofLp e * y.ofLp f) = 0 := by
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp_rw [sum_ite_prop_zero8]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fail "GOAL_OVERLAP"

-- SAME pair: pair_x = pair_y = {a,b}
set_option maxHeartbeats 4000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
      (if a = b then (1:ℝ) else 0) * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f *
      ((if a = b then (1:ℝ) else 0) * y.ofLp c * y.ofLp d * y.ofLp e * y.ofLp f) = 0 := by
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp_rw [sum_ite_prop_zero8]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fail "GOAL_SAME"

-- DISJOINT non-adjacent: pair_x = {a,e}, pair_y = {c,d}
set_option maxHeartbeats 4000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
      (if a = e then (1:ℝ) else 0) * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp f *
      ((if c = d then (1:ℝ) else 0) * y.ofLp a * y.ofLp b * y.ofLp e * y.ofLp f) = 0 := by
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp_rw [sum_ite_prop_zero8]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fail "GOAL_DISJOINT2"

end
