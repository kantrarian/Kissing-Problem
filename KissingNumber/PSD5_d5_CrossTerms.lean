import KissingNumber.Gegenbauer5
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

-- ============================================================
-- Helper lemmas (dimension 5)
-- ============================================================

private lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 5, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 5, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

private lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 5)) :
    @inner ℝ _ _ x y = ∑ a : Fin 5, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]
  congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

private lemma sum_ite_const_zero {p : Prop} [Decidable p] (f : Fin 5 → ℝ) :
    ∑ x : Fin 5, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

private lemma factor2 (f g : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, f a * g b =
    (∑ a : Fin 5, f a) * (∑ b : Fin 5, g b) := by
  rw [Finset.sum_mul]; congr 1; ext a; rw [Finset.mul_sum]

private lemma factor2_swap (f g : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, f b * g a =
    (∑ b : Fin 5, f b) * (∑ a : Fin 5, g a) := by
  rw [Finset.sum_comm]; exact factor2 f g

private lemma factor3 (f g h : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, f a * g b * h c =
    (∑ a : Fin 5, f a) * (∑ b : Fin 5, g b) * (∑ c : Fin 5, h c) := by
  calc ∑ a, ∑ b, ∑ c, f a * g b * h c
      = ∑ a, ∑ b, f a * g b * ∑ c, h c := by
        congr 1; ext a; congr 1; ext b; rw [← Finset.mul_sum]
    _ = ∑ a, f a * ((∑ b, g b) * (∑ c, h c)) := by
        congr 1; ext a
        simp_rw [show ∀ b, f a * g b * (∑ c, h c) = f a * (g b * (∑ c, h c)) from
          fun b => by ring]
        rw [← Finset.mul_sum, Finset.sum_mul]
    _ = (∑ a, f a) * ((∑ b, g b) * (∑ c, h c)) := by rw [← Finset.sum_mul]
    _ = _ := by ring

private lemma factor4 (f g h k : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5,
      f a * g b * h c * k d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, k d) := by
  trans (∑ a, f a) * ∑ b, ∑ c, ∑ d, g b * h c * k d
  · rw [Finset.sum_mul]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext b
    rw [Finset.mul_sum]; congr 1; ext c
    rw [Finset.mul_sum]; congr 1; ext d; ring
  · rw [factor3]; ring

-- ============================================================
-- Definitions: A5, B5, C5 for degree-5 trace-free tensors (d=5)
-- ============================================================

/-- Raw 5th moment tensor: x_a * x_b * x_c * x_d * x_e -/
private def A5 (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2.1 * x p.2.2.2.1 * x p.2.2.2.2

/-- 1-delta correction: C(5,2) = 10 terms, each = (3 x-coords) × δ_{pair} -/
private def B5 (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
    x p.2.2.1 * x p.2.2.2.1 * x p.2.2.2.2 * (if p.1 = p.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.2.1 * x p.2.2.2.2 * (if p.1 = p.2.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.1 * x p.2.2.2.2 * (if p.1 = p.2.2.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.1 * x p.2.2.2.1 * (if p.1 = p.2.2.2.2 then 1 else 0)
  + x p.1 * x p.2.2.2.1 * x p.2.2.2.2 * (if p.2.1 = p.2.2.1 then 1 else 0)
  + x p.1 * x p.2.2.1 * x p.2.2.2.2 * (if p.2.1 = p.2.2.2.1 then 1 else 0)
  + x p.1 * x p.2.2.1 * x p.2.2.2.1 * (if p.2.1 = p.2.2.2.2 then 1 else 0)
  + x p.1 * x p.2.1 * x p.2.2.2.2 * (if p.2.2.1 = p.2.2.2.1 then 1 else 0)
  + x p.1 * x p.2.1 * x p.2.2.2.1 * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
  + x p.1 * x p.2.1 * x p.2.2.1 * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)

/-- 2-delta correction: 15 terms = 5 unpaired × 3 pairings of remaining 4 -/
private def C5 (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  -- unpaired a (p.1)
    x p.1 * ((if p.2.1 = p.2.2.1 then 1 else 0) * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)
           + (if p.2.1 = p.2.2.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
           + (if p.2.1 = p.2.2.2.2 then 1 else 0) * (if p.2.2.1 = p.2.2.2.1 then 1 else 0))
  -- unpaired b (p.2.1)
  + x p.2.1 * ((if p.1 = p.2.2.1 then 1 else 0) * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)
             + (if p.1 = p.2.2.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
             + (if p.1 = p.2.2.2.2 then 1 else 0) * (if p.2.2.1 = p.2.2.2.1 then 1 else 0))
  -- unpaired c (p.2.2.1)
  + x p.2.2.1 * ((if p.1 = p.2.1 then 1 else 0) * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)
               + (if p.1 = p.2.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2.2 then 1 else 0)
               + (if p.1 = p.2.2.2.2 then 1 else 0) * (if p.2.1 = p.2.2.2.1 then 1 else 0))
  -- unpaired d (p.2.2.2.1)
  + x p.2.2.2.1 * ((if p.1 = p.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
                  + (if p.1 = p.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2.2 then 1 else 0)
                  + (if p.1 = p.2.2.2.2 then 1 else 0) * (if p.2.1 = p.2.2.1 then 1 else 0))
  -- unpaired e (p.2.2.2.2)
  + x p.2.2.2.2 * ((if p.1 = p.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.1 then 1 else 0)
                  + (if p.1 = p.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2.1 then 1 else 0)
                  + (if p.1 = p.2.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.1 then 1 else 0))

-- ============================================================
-- phi5 and product expansion
-- ============================================================

private def phi5 (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  A5 x p - (1 : ℝ) / 11 * B5 x p + (1 : ℝ) / 99 * C5 x p

private lemma phi5_product (x y : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) :
    phi5 x p * phi5 y p =
    A5 x p * A5 y p
    - (1/11) * (A5 x p * B5 y p + B5 x p * A5 y p)
    + (1/99) * (A5 x p * C5 y p + C5 x p * A5 y p)
    + (1/121) * (B5 x p * B5 y p)
    - (1/1089) * (B5 x p * C5 y p + C5 x p * B5 y p)
    + (1/9801) * (C5 x p * C5 y p) := by
  simp only [phi5]; ring

-- ============================================================
-- Cross-term sums
-- ============================================================

private lemma sum_AA (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, A5 x p * A5 y p =
    (@inner ℝ _ _ x y) ^ 5 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [A5]
  simp_rw [Fintype.sum_prod_type]
  -- Step 1: peel off innermost sum (over e)
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
    rw [show ∑ e : Fin 5,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) *
        ∑ e : Fin 5, x.ofLp e * y.ofLp e
        from by rw [Finset.mul_sum]; congr 1; ext e; ring]
  simp_rw [← hs]
  -- Step 2: peel off sum over d
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c
    rw [show ∑ d : Fin 5,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * s =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * s *
        ∑ d : Fin 5, x.ofLp d * y.ofLp d
        from by rw [Finset.mul_sum]; congr 1; ext d; ring]
  simp_rw [← hs]
  -- Step 3: peel off sum over c
  conv_lhs =>
    arg 2; ext a; arg 2; ext b
    rw [show ∑ c : Fin 5,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * s * s =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s * s *
        ∑ c : Fin 5, x.ofLp c * y.ofLp c
        from by rw [Finset.mul_sum]; congr 1; ext c; ring]
  simp_rw [← hs]
  -- Step 4: peel off sum over b
  conv_lhs =>
    arg 2; ext a
    rw [show ∑ b : Fin 5,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s * s * s =
        x.ofLp a * y.ofLp a * s * s * s *
        ∑ b : Fin 5, x.ofLp b * y.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
  simp_rw [← hs]
  -- Final: ∑_a x_a*y_a * s^4 = s * s^4 = s^5
  rw [show ∑ a : Fin 5, x.ofLp a * y.ofLp a * s * s * s * s =
      (∑ a, x.ofLp a * y.ofLp a) * s * s * s * s from by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]]
  rw [← hs]; ring

set_option maxHeartbeats 800000 in
private lemma sum_AB (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, A5 x p * B5 y p =
    10 * (@inner ℝ _ _ x y) ^ 3 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A5, B5]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  -- 4 canonical AC-normal forms
  have kA : ∀ a b c d : Fin 5,
      x.ofLp a * (x.ofLp a * (x.ofLp b * (x.ofLp c * (x.ofLp d *
        (y.ofLp b * (y.ofLp c * y.ofLp d)))))) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) := by intros; ring
  have kB : ∀ a b c d : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp b * (x.ofLp c * (x.ofLp d *
        (y.ofLp a * (y.ofLp c * y.ofLp d)))))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) := by intros; ring
  have kC : ∀ a b c d : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp c * (x.ofLp c * (x.ofLp d *
        (y.ofLp a * (y.ofLp b * y.ofLp d)))))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) *
        (x.ofLp d * y.ofLp d) := by intros; ring
  have kD : ∀ a b c d : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp c * (x.ofLp d * (x.ofLp d *
        (y.ofLp a * (y.ofLp b * y.ofLp c)))))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * x.ofLp d) := by intros; ring
  simp_rw [kA, kB, kC, kD, factor4, hxn, ← hs]
  ring

private lemma sum_BA (x y : EuclideanSpace ℝ (Fin 5)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5 x p * A5 y p =
    10 * (@inner ℝ _ _ x y) ^ 3 := by
  rw [show @inner ℝ _ _ x y = @inner ℝ _ _ y x from real_inner_comm y x]
  simp_rw [show ∀ p, B5 x p * A5 y p = A5 y p * B5 x p from fun p => mul_comm _ _]
  exact sum_AB y x hy

private lemma sum_AC (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, A5 x p * C5 y p =
    15 * @inner ℝ _ _ x y := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A5, C5]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  -- All 15 triple sums now have one of 3 canonical forms:
  have k1 : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp b * (x.ofLp c * (x.ofLp c * y.ofLp a)))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by
    intros; ring
  have k2 : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp a * (x.ofLp b * (x.ofLp c * (x.ofLp c * y.ofLp b)))) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) := by
    intros; ring
  have k3 : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp a * (x.ofLp b * (x.ofLp b * (x.ofLp c * y.ofLp c)))) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  simp_rw [k1, k2, k3, factor3, hxn, ← hs]
  ring

private lemma sum_CA (x y : EuclideanSpace ℝ (Fin 5)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, C5 x p * A5 y p =
    15 * @inner ℝ _ _ x y := by
  rw [show @inner ℝ _ _ x y = @inner ℝ _ _ y x from real_inner_comm y x]
  simp_rw [show ∀ p, C5 x p * A5 y p = A5 y p * C5 x p from fun p => mul_comm _ _]
  exact sum_AC y x hy

-- ============================================================
-- BB decomposition: split B5 = B5a + B5b
-- B5a: 4 terms where delta involves position a (p.1)
-- B5b: 6 terms where delta is among positions b,c,d,e
-- ============================================================

private def B5a (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
    x p.2.2.1 * x p.2.2.2.1 * x p.2.2.2.2 * (if p.1 = p.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.2.1 * x p.2.2.2.2 * (if p.1 = p.2.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.1 * x p.2.2.2.2 * (if p.1 = p.2.2.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.1 * x p.2.2.2.1 * (if p.1 = p.2.2.2.2 then 1 else 0)

private def B5b (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
    x p.1 * x p.2.2.2.1 * x p.2.2.2.2 * (if p.2.1 = p.2.2.1 then 1 else 0)
  + x p.1 * x p.2.2.1 * x p.2.2.2.2 * (if p.2.1 = p.2.2.2.1 then 1 else 0)
  + x p.1 * x p.2.2.1 * x p.2.2.2.1 * (if p.2.1 = p.2.2.2.2 then 1 else 0)
  + x p.1 * x p.2.1 * x p.2.2.2.2 * (if p.2.2.1 = p.2.2.2.1 then 1 else 0)
  + x p.1 * x p.2.1 * x p.2.2.2.1 * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
  + x p.1 * x p.2.1 * x p.2.2.1 * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)

private lemma B5_split (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) :
    B5 x p = B5a x p + B5b x p := by
  simp only [B5, B5a, B5b]; ring

-- ============================================================
-- BB sub-sums
-- ============================================================

set_option maxHeartbeats 1600000 in
private lemma sum_B5aa (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5a x p * B5a y p =
    32 * (@inner ℝ _ _ x y) ^ 3 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [B5a]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  have kA : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp c * (y.ofLp a * (y.ofLp b * y.ofLp c)))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  simp_rw [kA, factor3, ← hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

set_option maxHeartbeats 3200000 in
private lemma sum_B5ab (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5a x p * B5b y p =
    12 * (@inner ℝ _ _ x y) ^ 3 + 12 * @inner ℝ _ _ x y := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [B5a, B5b]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000 }) only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  -- k-lemmas: rewrite AC-normalized products to factored form
  have kA : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp c * (y.ofLp a * (y.ofLp b * y.ofLp c)))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have kB : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp a * (x.ofLp c * (y.ofLp b * (y.ofLp b * y.ofLp c)))) =
      (x.ofLp a * x.ofLp a) * (y.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have kC : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp b * (y.ofLp c * (y.ofLp c * y.ofLp a)))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (y.ofLp c * y.ofLp c) := by
    intros; ring
  simp_rw [kA, kB, kC]
  -- Three types of triple sums:
  have v1 : ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5,
      x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) = s ^ 3 := by
    trans (∑ a, x.ofLp a * y.ofLp a) * (∑ b, x.ofLp b * y.ofLp b) * (∑ c, x.ofLp c * y.ofLp c)
    · exact factor3 _ _ _
    · rw [← hs]; ring
  have v2 : ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5,
      x.ofLp b * x.ofLp b * (y.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) = s := by
    conv_lhs => rw [Finset.sum_comm]
    trans (∑ b, x.ofLp b * x.ofLp b) * (∑ a, y.ofLp a * y.ofLp a) * (∑ c, x.ofLp c * y.ofLp c)
    · exact factor3 _ _ _
    · rw [hxn, hyn, ← hs]; ring
  have v3 : ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5,
      x.ofLp b * y.ofLp b * (x.ofLp c * x.ofLp c) * (y.ofLp a * y.ofLp a) = s := by
    conv_lhs =>
      rw [Finset.sum_comm]
      arg 2; ext b; rw [Finset.sum_comm]
    trans (∑ b, x.ofLp b * y.ofLp b) * (∑ c, x.ofLp c * x.ofLp c) * (∑ a, y.ofLp a * y.ofLp a)
    · exact factor3 _ _ _
    · rw [hxn, hyn, ← hs]; ring
  simp only [v1, v2, v3]
  ring

set_option maxHeartbeats 6400000 in
private lemma sum_B5bb (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5b x p * B5b y p =
    54 * (@inner ℝ _ _ x y) ^ 3 + 6 * @inner ℝ _ _ x y := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [B5b]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 600000 }) only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  have kA : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp c * (y.ofLp a * (y.ofLp b * y.ofLp c)))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have kB : ∀ a b c : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp b * (y.ofLp a * (y.ofLp c * y.ofLp c)))) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (y.ofLp c * y.ofLp c) := by
    intros; ring
  simp_rw [kA, kB]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  simp only [← hs, hxn, hyn]
  simp only [mul_one]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp only [← hs, hxn, hyn]
  simp_rw [← Finset.sum_mul]
  simp only [← hs]
  ring

private lemma sum_BB (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5 x p * B5 y p =
    110 * (@inner ℝ _ _ x y) ^ 3 + 30 * @inner ℝ _ _ x y := by
  simp_rw [B5_split]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [sum_B5aa x y, sum_B5ab x y hx hy,
      show ∑ p, B5b x p * B5a y p = ∑ p, B5a y p * B5b x p from by
        congr 1; ext p; ring,
      sum_B5ab y x hy hx,
      show @inner ℝ _ _ y x = @inner ℝ _ _ x y from real_inner_comm x y,
      sum_B5bb x y hx hy]
  ring

-- ============================================================
-- C5 decomposition and cross-terms
-- ============================================================

-- Each group of C5: "unpaired" coordinate times 3 delta-pair products
private def C5a (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.1 * ((if p.2.1 = p.2.2.1 then 1 else 0) * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)
         + (if p.2.1 = p.2.2.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
         + (if p.2.1 = p.2.2.2.2 then 1 else 0) * (if p.2.2.1 = p.2.2.2.1 then 1 else 0))

private def C5b (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.2.1 * ((if p.1 = p.2.2.1 then 1 else 0) * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)
           + (if p.1 = p.2.2.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
           + (if p.1 = p.2.2.2.2 then 1 else 0) * (if p.2.2.1 = p.2.2.2.1 then 1 else 0))

private def C5c (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.2.2.1 * ((if p.1 = p.2.1 then 1 else 0) * (if p.2.2.2.1 = p.2.2.2.2 then 1 else 0)
             + (if p.1 = p.2.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2.2 then 1 else 0)
             + (if p.1 = p.2.2.2.2 then 1 else 0) * (if p.2.1 = p.2.2.2.1 then 1 else 0))

private def C5d (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.2.2.2.1 * ((if p.1 = p.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.2 then 1 else 0)
                + (if p.1 = p.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2.2 then 1 else 0)
                + (if p.1 = p.2.2.2.2 then 1 else 0) * (if p.2.1 = p.2.2.1 then 1 else 0))

private def C5e (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.2.2.2.2 * ((if p.1 = p.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2.1 then 1 else 0)
                + (if p.1 = p.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2.1 then 1 else 0)
                + (if p.1 = p.2.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.1 then 1 else 0))

private lemma C5_split (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) :
    C5 x p = C5a x p + C5b x p + C5c x p + C5d x p + C5e x p := by
  simp only [C5, C5a, C5b, C5c, C5d, C5e]

-- Swap equivalences for 5-tuples
private def swapAB : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨b, a, c, d, e⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨b, a, c, d, e⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

private def swapAC : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨c, b, a, d, e⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨c, b, a, d, e⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

private def swapAD : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨d, b, c, a, e⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨d, b, c, a, e⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

private def swapAE : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨e, b, c, d, a⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨e, b, c, d, a⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

private def swapBC : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨a, c, b, d, e⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨a, c, b, d, e⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

private def swapBD : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨a, d, c, b, e⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨a, d, c, b, e⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

private def swapBE : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) where
  toFun := fun ⟨a, b, c, d, e⟩ => ⟨a, e, c, d, b⟩
  invFun := fun ⟨a, b, c, d, e⟩ => ⟨a, e, c, d, b⟩
  left_inv := fun ⟨_, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _⟩ => rfl

-- Application lemmas for swap Equivs
private lemma swapAB_apply (a b c d e : Fin 5) :
    swapAB (a, b, c, d, e) = (b, a, c, d, e) := rfl
private lemma swapAC_apply (a b c d e : Fin 5) :
    swapAC (a, b, c, d, e) = (c, b, a, d, e) := rfl
private lemma swapAD_apply (a b c d e : Fin 5) :
    swapAD (a, b, c, d, e) = (d, b, c, a, e) := rfl
private lemma swapAE_apply (a b c d e : Fin 5) :
    swapAE (a, b, c, d, e) = (e, b, c, d, a) := rfl
private lemma swapBC_apply (a b c d e : Fin 5) :
    swapBC (a, b, c, d, e) = (a, c, b, d, e) := rfl
private lemma swapBD_apply (a b c d e : Fin 5) :
    swapBD (a, b, c, d, e) = (a, d, c, b, e) := rfl
private lemma swapBE_apply (a b c d e : Fin 5) :
    swapBE (a, b, c, d, e) = (a, e, c, d, b) := rfl

-- Helper: normalize reversed equality in ite conditions
private lemma ite_eqc (a b : Fin 5) :
    (if a = b then (1:ℝ) else 0) = (if b = a then 1 else 0) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : b ≠ a := fun hba => h hba.symm; simp [h, h']

-- Key identity: C5i(z, swap(p)) = C5a(z, p) for diagonal swaps
private lemma C5b_eq_C5a_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5b z p = C5a z (swapAB p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5b, C5a, swapAB_apply]

private lemma C5c_eq_C5a_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5c z p = C5a z (swapAC p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5c, C5a, swapAC_apply]
  rw [ite_eqc b a]; ring

private lemma C5d_eq_C5a_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5d z p = C5a z (swapAD p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5d, C5a, swapAD_apply]
  rw [ite_eqc b a, ite_eqc c a]; ring

private lemma C5e_eq_C5a_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5e z p = C5a z (swapAE p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5e, C5a, swapAE_apply]
  rw [ite_eqc b a, ite_eqc c a, ite_eqc d a]; ring

-- B5 is symmetric in all 5 positions
private lemma B5_inv_swapAB (x : EuclideanSpace ℝ (Fin 5)) (p) :
    B5 x (swapAB p) = B5 x p := by
  obtain ⟨a,b,c,d,e⟩ := p; simp only [B5, swapAB_apply]
  rw [ite_eqc b a]; ring

private lemma B5_inv_swapAC (x : EuclideanSpace ℝ (Fin 5)) (p) :
    B5 x (swapAC p) = B5 x p := by
  obtain ⟨a,b,c,d,e⟩ := p; simp only [B5, swapAC_apply]
  rw [ite_eqc c b, ite_eqc c a, ite_eqc b a]; ring

private lemma B5_inv_swapAD (x : EuclideanSpace ℝ (Fin 5)) (p) :
    B5 x (swapAD p) = B5 x p := by
  obtain ⟨a,b,c,d,e⟩ := p; simp only [B5, swapAD_apply]
  rw [ite_eqc d b, ite_eqc d c, ite_eqc d a, ite_eqc b a, ite_eqc c a]; ring

private lemma B5_inv_swapAE (x : EuclideanSpace ℝ (Fin 5)) (p) :
    B5 x (swapAE p) = B5 x p := by
  obtain ⟨a,b,c,d,e⟩ := p; simp only [B5, swapAE_apply]
  rw [ite_eqc e b, ite_eqc e c, ite_eqc e d, ite_eqc e a, ite_eqc b a, ite_eqc c a, ite_eqc d a]; ring

-- Helper: ∑ B5*C5i = ∑ B5*C5a via symmetry
private lemma sum_B5_C5i_eq_C5a (x y : EuclideanSpace ℝ (Fin 5))
    (C5i : EuclideanSpace ℝ (Fin 5) →
      (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) → ℝ)
    (σ : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
      (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5))
    (hB : ∀ p, B5 x (σ p) = B5 x p)
    (hC : ∀ p, C5i y p = C5a y (σ p)) :
    ∑ p, B5 x p * C5i y p = ∑ p, B5 x p * C5a y p := by
  simp_rw [hC]
  exact Fintype.sum_equiv σ _ _ (fun p => by rw [hB])

-- Sub-sum: ∑ B5×C5a = 54s (for d=5)
set_option maxHeartbeats 6400000 in
private lemma sum_B5_C5a (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5 x p * C5a y p =
    54 * @inner ℝ _ _ x y := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [B5, C5a]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 2000000 }) only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  have kB : ∀ a b : Fin 5,
      x.ofLp a * (x.ofLp b * (x.ofLp b * y.ofLp a)) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [kB]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  simp only [← hs, hxn]
  simp only [mul_one]
  simp only [← hs]
  ring

-- BC = 270s (for d=5)
private lemma sum_BC (x : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1)
    (y : EuclideanSpace ℝ (Fin 5)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, B5 x p * C5 y p =
    270 * @inner ℝ _ _ x y := by
  simp_rw [C5_split]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_B5_C5i_eq_C5a x y C5b swapAB (B5_inv_swapAB x) (C5b_eq_C5a_swap y),
      sum_B5_C5i_eq_C5a x y C5c swapAC (B5_inv_swapAC x) (C5c_eq_C5a_swap y),
      sum_B5_C5i_eq_C5a x y C5d swapAD (B5_inv_swapAD x) (C5d_eq_C5a_swap y),
      sum_B5_C5i_eq_C5a x y C5e swapAE (B5_inv_swapAE x) (C5e_eq_C5a_swap y),
      sum_B5_C5a x y hx]
  ring

private lemma sum_CB (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, C5 x p * B5 y p =
    270 * @inner ℝ _ _ x y := by
  rw [show @inner ℝ _ _ x y = @inner ℝ _ _ y x from real_inner_comm y x]
  simp_rw [show ∀ p, C5 x p * B5 y p = B5 y p * C5 x p from fun p => mul_comm _ _]
  exact sum_BC y hy x hx

-- ============================================================
-- CC = 945s (for d=5)
-- ============================================================

-- Diagonal sum identities via Fintype.sum_equiv
private lemma sum_C5ii_eq_aa (z w : EuclideanSpace ℝ (Fin 5))
    (C5i : EuclideanSpace ℝ (Fin 5) →
      (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) → ℝ)
    (σ : (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃
      (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5))
    (h : ∀ u p, C5i u p = C5a u (σ p)) :
    ∑ p, C5i z p * C5i w p = ∑ p, C5a z p * C5a w p := by
  simp_rw [h]
  exact Fintype.sum_equiv σ _ _ (fun p => rfl)

-- Cross-term: same-unpaired (a,a). Result = 135s (for d=5: 3*25 + 6*5 = 75 + 30..., but per-x factor)
set_option maxHeartbeats 800000 in
private lemma sum_C5aa (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, C5a x p * C5a y p =
    105 * @inner ℝ _ _ x y := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [C5a]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum, ← hs]
  ring

-- Cross-term: diff-unpaired (a,b). Result = 27s (for d=5)
set_option maxHeartbeats 800000 in
private lemma sum_C5ab (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, C5a x p * C5b y p =
    21 * @inner ℝ _ _ x y := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [C5a, C5b]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    sum_ite_const_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum, ← hs]
  ring

-- For off-diagonal: C5j(z, swap(p)) = C5b(z, p) when we swap j's position with b
private lemma C5c_eq_C5b_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5c z p = C5b z (swapBC p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5c, C5b, swapBC_apply]

private lemma C5d_eq_C5b_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5d z p = C5b z (swapBD p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5d, C5b, swapBD_apply]
  rw [ite_eqc c b]; ring

private lemma C5e_eq_C5b_swap (z : EuclideanSpace ℝ (Fin 5)) (p) :
    C5e z p = C5b z (swapBE p) := by
  obtain ⟨a, b, c, d, e⟩ := p; simp only [C5e, C5b, swapBE_apply]
  rw [ite_eqc c b, ite_eqc d b]; ring

-- Helper: any cross-term with C5a on one side and C5j on other = sum_C5ab
private lemma sum_C5a_C5c (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5a x p * C5c y p = ∑ p, C5a x p * C5b y p := by
  simp_rw [C5c_eq_C5b_swap]
  exact (Fintype.sum_equiv swapBC _ _ (fun ⟨a,b,c,d,e⟩ => by
    simp only [swapBC_apply, C5a]; rw [ite_eqc c b]; ring)).symm

private lemma sum_C5a_C5d (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5a x p * C5d y p = ∑ p, C5a x p * C5b y p := by
  simp_rw [C5d_eq_C5b_swap]
  exact (Fintype.sum_equiv swapBD _ _ (fun ⟨a,b,c,d,e⟩ => by
    simp only [swapBD_apply, C5a]; rw [ite_eqc d b, ite_eqc b c, ite_eqc c d]; ring)).symm

private lemma sum_C5a_C5e (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5a x p * C5e y p = ∑ p, C5a x p * C5b y p := by
  simp_rw [C5e_eq_C5b_swap]
  exact (Fintype.sum_equiv swapBE _ _ (fun ⟨a,b,c,d,e⟩ => by
    simp only [swapBE_apply, C5a]; rw [ite_eqc e b, ite_eqc e c, ite_eqc d b, ite_eqc e d, ite_eqc c b]; ring)).symm

-- Reverse helper: ∑ C5j×C5i = 27s from ∑ C5i×C5j = 27s
private lemma sum_C5_rev {C5i C5j : EuclideanSpace ℝ (Fin 5) →
    (Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) → ℝ}
    (h : ∀ x y : EuclideanSpace ℝ (Fin 5),
      ∑ p, C5i x p * C5j y p = 21 * @inner ℝ _ _ x y)
    (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5j x p * C5i y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5j x p * C5i y p = ∑ p, C5i y p * C5j x p from by
        congr 1; ext; ring,
      h y x, real_inner_comm y x]

-- Off-diagonal sums between non-a groups (via swap + invariance)
private lemma sum_C5b_C5c (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5b x p * C5c y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5b x p * C5c y p = ∑ p, C5a x p * C5c y p from
    (Fintype.sum_equiv swapAB _ _ (fun ⟨a,b,c,d,e⟩ => by
      simp only [C5a, C5b, C5c, swapAB_apply]; rw [ite_eqc b a]; ring)).symm,
    sum_C5a_C5c, sum_C5ab]

private lemma sum_C5b_C5d (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5b x p * C5d y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5b x p * C5d y p = ∑ p, C5a x p * C5d y p from
    (Fintype.sum_equiv swapAB _ _ (fun ⟨a,b,c,d,e⟩ => by
      simp only [C5a, C5b, C5d, swapAB_apply]; rw [ite_eqc b a]; ring)).symm,
    sum_C5a_C5d, sum_C5ab]

private lemma sum_C5b_C5e (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5b x p * C5e y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5b x p * C5e y p = ∑ p, C5a x p * C5e y p from
    (Fintype.sum_equiv swapAB _ _ (fun ⟨a,b,c,d,e⟩ => by
      simp only [C5a, C5b, C5e, swapAB_apply]; rw [ite_eqc b a]; ring)).symm,
    sum_C5a_C5e, sum_C5ab]

private lemma sum_C5c_C5d (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5c x p * C5d y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5c x p * C5d y p = ∑ p, C5a x p * C5d y p from
    (Fintype.sum_equiv swapAC _ _ (fun ⟨a,b,c,d,e⟩ => by
      simp only [C5a, C5c, C5d, swapAC_apply]; rw [ite_eqc c b, ite_eqc c a, ite_eqc b a]; ring)).symm,
    sum_C5a_C5d, sum_C5ab]

private lemma sum_C5c_C5e (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5c x p * C5e y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5c x p * C5e y p = ∑ p, C5a x p * C5e y p from
    (Fintype.sum_equiv swapAC _ _ (fun ⟨a,b,c,d,e⟩ => by
      simp only [C5a, C5c, C5e, swapAC_apply]; rw [ite_eqc c b, ite_eqc c a, ite_eqc b a]; ring)).symm,
    sum_C5a_C5e, sum_C5ab]

private lemma sum_C5d_C5e (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p, C5d x p * C5e y p = 21 * @inner ℝ _ _ x y := by
  rw [show ∑ p, C5d x p * C5e y p = ∑ p, C5a x p * C5e y p from
    (Fintype.sum_equiv swapAD _ _ (fun ⟨a,b,c,d,e⟩ => by
      simp only [C5a, C5d, C5e, swapAD_apply]; rw [ite_eqc d b, ite_eqc d c, ite_eqc d a, ite_eqc c a, ite_eqc b a]; ring)).symm,
    sum_C5a_C5e, sum_C5ab]

private lemma sum_CC (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, C5 x p * C5 y p =
    945 * @inner ℝ _ _ x y := by
  -- Expand C5 into 5 groups
  simp_rw [C5_split]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  -- All 5 diagonal terms = sum_C5aa = 135s
  rw [sum_C5ii_eq_aa x y C5b swapAB C5b_eq_C5a_swap,
      sum_C5ii_eq_aa x y C5c swapAC C5c_eq_C5a_swap,
      sum_C5ii_eq_aa x y C5d swapAD C5d_eq_C5a_swap,
      sum_C5ii_eq_aa x y C5e swapAE C5e_eq_C5a_swap,
      sum_C5aa]
  -- Off-diagonal terms with C5a on the left
  rw [sum_C5a_C5c, sum_C5a_C5d, sum_C5a_C5e, sum_C5ab]
  -- Off-diagonal terms with C5a on the right (swap x↔y and use mul_comm)
  rw [show ∑ p, C5b x p * C5a y p = ∑ p, C5a y p * C5b x p from by
        congr 1; ext; ring,
      show ∑ p, C5c x p * C5a y p = ∑ p, C5a y p * C5c x p from by
        congr 1; ext; ring,
      show ∑ p, C5d x p * C5a y p = ∑ p, C5a y p * C5d x p from by
        congr 1; ext; ring,
      show ∑ p, C5e x p * C5a y p = ∑ p, C5a y p * C5e x p from by
        congr 1; ext; ring,
      sum_C5a_C5c y x, sum_C5a_C5d y x, sum_C5a_C5e y x, sum_C5ab y x,
      show @inner ℝ _ _ y x = @inner ℝ _ _ x y from real_inner_comm x y]
  -- 12 off-diagonal terms between non-a groups (b,c,d,e pairs)
  -- 6 forward pairs
  rw [sum_C5b_C5c, sum_C5b_C5d, sum_C5b_C5e,
      sum_C5c_C5d, sum_C5c_C5e, sum_C5d_C5e]
  -- 6 reverse pairs
  rw [sum_C5_rev sum_C5b_C5c, sum_C5_rev sum_C5b_C5d,
      sum_C5_rev sum_C5b_C5e, sum_C5_rev sum_C5c_C5d,
      sum_C5_rev sum_C5c_C5e, sum_C5_rev sum_C5d_C5e]
  ring

-- ============================================================
-- Main kernel identity
-- ============================================================

private lemma phi5_kernel (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, phi5 x p * phi5 y p =
    (8 : ℝ) / 33 * P5 5 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, phi5 x p * phi5 y p =
      (@inner ℝ _ _ x y) ^ 5 - 10 / 11 * (@inner ℝ _ _ x y) ^ 3
      + 5 / 33 * @inner ℝ _ _ x y by
    rw [h, P5_5]; ring
  set s := @inner ℝ _ _ x y
  simp_rw [phi5_product]
  simp only [sub_eq_add_neg]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [sum_AA, sum_AB x y hx, sum_BA x y hy, sum_AC x y hx, sum_CA x y hy,
      sum_BB x y hx hy, sum_BC x hx y hy, sum_CB x y hx hy, sum_CC]
  ring

-- ============================================================
-- Public exports for use by PSD5.lean
-- ============================================================

def phi5_d5_Feature (x : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  phi5 x p

lemma phi5_d5_Feature_kernel (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5, phi5_d5_Feature x p * phi5_d5_Feature y p =
    (8 : ℝ) / 33 * P5 5 (@inner ℝ _ _ x y) := by
  simp only [phi5_d5_Feature]
  exact phi5_kernel x y hx hy

end
