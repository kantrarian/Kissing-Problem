import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

private lemma sum_ite_const_zero {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

set_option maxHeartbeats 800000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8,
      x.ofLp a * ((if b = c then (1:ℝ) else 0) * (if d = e then 1 else 0)
         + (if b = d then 1 else 0) * (if c = e then 1 else 0)
         + (if b = e then 1 else 0) * (if c = d then 1 else 0))
      * (y.ofLp a * ((if b = c then 1 else 0) * (if d = e then 1 else 0)
         + (if b = d then 1 else 0) * (if c = e then 1 else 0)
         + (if b = e then 1 else 0) * (if c = d then 1 else 0)))
    = 240 * ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d; arg 2; ext e
    rw [show x.ofLp a * ((if b = c then (1:ℝ) else 0) * (if d = e then 1 else 0)
         + (if b = d then 1 else 0) * (if c = e then 1 else 0)
         + (if b = e then 1 else 0) * (if c = d then 1 else 0))
      * (y.ofLp a * ((if b = c then 1 else 0) * (if d = e then 1 else 0)
         + (if b = d then 1 else 0) * (if c = e then 1 else 0)
         + (if b = e then 1 else 0) * (if c = d then 1 else 0)))
      = x.ofLp a * y.ofLp a *
        (((if b = c then (1:ℝ) else 0) * (if d = e then 1 else 0)
         + (if b = d then 1 else 0) * (if c = e then 1 else 0)
         + (if b = e then 1 else 0) * (if c = d then 1 else 0))
        * ((if b = c then 1 else 0) * (if d = e then 1 else 0)
         + (if b = d then 1 else 0) * (if c = e then 1 else 0)
         + (if b = e then 1 else 0) * (if c = d then 1 else 0)))
      from by ring]
  simp_rw [← Finset.mul_sum]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  exact (0 : Nat)

end
