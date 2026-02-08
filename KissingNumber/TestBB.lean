import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

private abbrev T6BB := Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8

private lemma ofLp_norm_sq_BB (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

private lemma inner_ofLp_BB (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]; congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

private lemma sum_ite_prop_zero_BB {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

private def B6BB (x : EuclideanSpace ℝ (Fin 8)) (p : T6BB) : ℝ :=
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

-- Extract goal state after delta collapse for BB
set_option maxHeartbeats 3200000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6BB, B6BB x p * B6BB y p =
    240 * (@inner ℝ _ _ x y) ^ 4 + 90 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp_BB x y
  have hxn := ofLp_norm_sq_BB x hx
  have hyn := ofLp_norm_sq_BB y hy
  simp only [B6BB]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 800000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 800000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero_BB]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  sorry

end
