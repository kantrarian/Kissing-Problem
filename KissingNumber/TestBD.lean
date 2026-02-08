import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

private abbrev T6 := Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8

private lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

private lemma sum_ite_prop_zero {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

private lemma factor2 (f g : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, f a * g b =
    (∑ a, f a) * (∑ b, g b) := by
  rw [Finset.sum_mul]; congr 1; ext a; rw [← Finset.mul_sum]

private def B6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if a = b then 1 else 0) * x c * x d * x e * x f
  + (if a = c then 1 else 0) * x b * x d * x e * x f
  + (if a = d then 1 else 0) * x b * x c * x e * x f
  + (if a = e then 1 else 0) * x b * x c * x d * x f
  + (if a = f then 1 else 0) * x b * x c * x d * x e
  + (if b = c then 1 else 0) * x a * x d * x e * x f
  + (if b = d then 1 else 0) * x a * x c * x e * x f
  + (if b = e then 1 else 0) * x a * x c * x d * x f
  + (if b = f then 1 else 0) * x a * x c * x d * x e
  + (if c = d then 1 else 0) * x a * x b * x e * x f
  + (if c = e then 1 else 0) * x a * x b * x d * x f
  + (if c = f then 1 else 0) * x a * x b * x d * x e
  + (if d = e then 1 else 0) * x a * x b * x c * x f
  + (if d = f then 1 else 0) * x a * x b * x c * x e
  + (if e = f then 1 else 0) * x a * x b * x c * x d

private def D6 (_x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if a=b then 1 else 0) * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + (if a=c then 1 else 0) * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  + (if a=d then 1 else 0) * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + (if a=e then 1 else 0) * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + (if a=f then 1 else 0) * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))

-- Test: sum_BD with brute-force delta collapse
set_option maxHeartbeats 800000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6, B6 x p * D6 y p = 540 := by
  have hxn := ofLp_norm_sq x hx
  simp only [B6, D6]
  simp_rw [Fintype.sum_prod_type]
  -- Distribute: 15 * 15 = 225 terms
  simp (config := { maxSteps := 200000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  -- Handle ite multiplication
  simp (config := { maxSteps := 200000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  -- Delta collapse - 5 rounds (to handle deltas at all positions)
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- After full collapse, should have sums of x-squares
  -- Each surviving term: x_i^2 * x_j^2 → factor2 + hxn^2 = 1
  -- Or just x_i^2 → hxn = 1
  -- Try to close with rearrangement and factoring
  have r1 : ∀ a b : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r3 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, factor2, hxn]
  norm_num

end
