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

private lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]; congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

private lemma sum_ite_prop_zero {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

private lemma factor4 (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, f a * g b * h c * j d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

private def A6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2.1 * x p.2.2.2.1 * x p.2.2.2.2.1 * x p.2.2.2.2.2

private def C6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x a * x b * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x c * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x d * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + x a * x e * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + x a * x f * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))
  + x b * x c * ((if a=d then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if d=f then 1 else 0) + (if a=f then 1 else 0)*(if d=e then 1 else 0))
  + x b * x d * ((if a=c then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=e then 1 else 0))
  + x b * x e * ((if a=c then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=d then 1 else 0))
  + x b * x f * ((if a=c then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if c=e then 1 else 0) + (if a=e then 1 else 0)*(if c=d then 1 else 0))
  + x c * x d * ((if a=b then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=e then 1 else 0))
  + x c * x e * ((if a=b then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=d then 1 else 0))
  + x c * x f * ((if a=b then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=d then 1 else 0))
  + x d * x e * ((if a=b then 1 else 0)*(if c=f then 1 else 0) + (if a=c then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=c then 1 else 0))
  + x d * x f * ((if a=b then 1 else 0)*(if c=e then 1 else 0) + (if a=c then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=c then 1 else 0))
  + x e * x f * ((if a=b then 1 else 0)*(if c=d then 1 else 0) + (if a=c then 1 else 0)*(if b=d then 1 else 0) + (if a=d then 1 else 0)*(if b=c then 1 else 0))

-- Test: delta collapse + simp only [sq] + rearrangement + factor4
set_option maxHeartbeats 102400000 in
example (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6, A6 x p * C6 y p =
    45 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A6, C6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 30000000 }) only [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Normalize x ^ 2 back to x * x (delta collapse introduces ^ 2)
  simp only [sq]
  -- Rearrangement lemmas
  have r1 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r2 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r3 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r4 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r5 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r6 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r7 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r8 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r9 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r10 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r11 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r12 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r13 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r14 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r15 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r16 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r17 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r18 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r19 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r20 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r21 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r22 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r23 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r24 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r25 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r26 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r27 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r28 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r29 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r30 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r31 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r32 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r33 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r34 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r35 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r36 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r37 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r38 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r39 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp a * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r40 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r41 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, factor4, hxn, ← hs]
  ring

end
