import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

private lemma sum_ite_prop_zero' {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

private lemma factor3' (f g h : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, f a * g b * h c =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

-- Test: 3-level delta collapse with sum_ite_prop_zero
set_option maxHeartbeats 800000 in
example (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
    x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f *
    ((if a = b then (1:ℝ) else 0) * ((if c = d then (1:ℝ) else 0) * (if e = f then (1:ℝ) else 0))) = 1 := by
  have hxn : ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
    have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
    have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
      rw [PiLp.inner_apply]; congr 1
    linarith
  -- Step 1: handle ite multiplication
  simp only [mul_ite, mul_zero, mul_one]
  -- Step 2: first delta collapse (innermost sum over f, condition e=f)
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 3: pull constant ifs outside sums, then collapse again
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 4: if needed, repeat
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Now should have: ∑ a, ∑ c, ∑ e, x_a * x_a * x_c * x_c * x_e * x_e = 1
  have k : ∀ a c e : Fin 8,
      x.ofLp a * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp e * x.ofLp e =
      (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) * (x.ofLp e * x.ofLp e) := by
    intros; ring
  simp_rw [k, factor3', hxn]; norm_num
