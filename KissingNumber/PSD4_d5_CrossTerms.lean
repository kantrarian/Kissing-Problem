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

-- Pull if out of a sum when condition is independent of summation variable
private lemma sum_ite_const_zero {p : Prop} [Decidable p] (f : Fin 5 → ℝ) :
    ∑ x : Fin 5, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

-- Factor a double sum of products
private lemma factor2 (f g : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, f a * g b =
    (∑ a : Fin 5, f a) * (∑ b : Fin 5, g b) := by
  rw [Finset.sum_mul]; congr 1; ext a; rw [Finset.mul_sum]

-- Factor a double sum where the inner variable comes first
private lemma factor2_swap (f g : Fin 5 → ℝ) :
    ∑ a : Fin 5, ∑ b : Fin 5, f b * g a =
    (∑ b : Fin 5, f b) * (∑ a : Fin 5, g a) := by
  rw [Finset.sum_comm]; exact factor2 f g

-- Factor a triple sum of products
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

-- ============================================================
-- Definitions (k=4, d=5)
-- ============================================================

private def A4 (x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2.1 * x p.2.2.2

private def B4 (x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
    x p.1 * x p.2.1 * (if p.2.2.1 = p.2.2.2 then 1 else 0)
  + x p.1 * x p.2.2.1 * (if p.2.1 = p.2.2.2 then 1 else 0)
  + x p.1 * x p.2.2.2 * (if p.2.1 = p.2.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.1 * (if p.1 = p.2.2.2 then 1 else 0)
  + x p.2.1 * x p.2.2.2 * (if p.1 = p.2.2.1 then 1 else 0)
  + x p.2.2.1 * x p.2.2.2 * (if p.1 = p.2.1 then 1 else 0)

private def C4 (_x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
    (if p.1 = p.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2 then 1 else 0)
  + (if p.1 = p.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2 then 1 else 0)
  + (if p.1 = p.2.2.2 then 1 else 0) * (if p.2.1 = p.2.2.1 then 1 else 0)

-- ============================================================
-- ∑ AC = 3
-- ============================================================

private lemma sum_AC (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, A4 x p * C4 y p = 3 := by
  have hxn := ofLp_norm_sq x hx
  simp only [A4, C4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- 3 double sums, each = (∑ x²)² = 1
  have k1 : ∀ a b : Fin 5, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have k2 : ∀ a b : Fin 5, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have k3 : ∀ a b : Fin 5, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [k1, k2, k3, factor2, hxn]
  norm_num

-- ∑ CA = 3
private lemma sum_CA (x y : EuclideanSpace ℝ (Fin 5)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, C4 x p * A4 y p = 3 := by
  simp_rw [show ∀ p, C4 x p * A4 y p = A4 y p * C4 x p from fun p => mul_comm _ _]
  exact sum_AC y x hy

-- ============================================================
-- ∑ AB = 6s²
-- ============================================================

private lemma sum_AB (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, A4 x p * B4 y p =
    6 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A4, B4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Rearrange each triple sum to f(a)*g(b)*h(c) form
  have k1 : ∀ a b c : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) := by
    intros; ring
  have k2 : ∀ a b c : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have k3 : ∀ a b c : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have k4 : ∀ a b c : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp c) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have k5 : ∀ a b c : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp c) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  have k6 : ∀ a b c : Fin 5,
      x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp b * y.ofLp c) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) := by
    intros; ring
  simp_rw [k1, k2, k3, k4, k5, k6, factor3]
  rw [hxn, ← hs]; ring

-- ∑ BA = 6s²
private lemma sum_BA (x y : EuclideanSpace ℝ (Fin 5)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, B4 x p * A4 y p =
    6 * (@inner ℝ _ _ x y) ^ 2 := by
  rw [show @inner ℝ _ _ x y = @inner ℝ _ _ y x from real_inner_comm y x]
  simp_rw [show ∀ p, B4 x p * A4 y p = A4 y p * B4 x p from fun p => mul_comm _ _]
  exact sum_AB y x hy

-- ============================================================
-- ∑ CC = 105 (= 3*25 + 6*5 for d=5)
-- ============================================================

private lemma sum_CC (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, C4 x p * C4 y p = 105 := by
  simp only [C4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const]
  norm_num

-- ============================================================
-- ∑ AA = s⁴
-- ============================================================

private lemma sum_AA (x y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, A4 x p * A4 y p =
    (@inner ℝ _ _ x y) ^ 4 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [A4]
  simp_rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c
    rw [show ∑ d : Fin 5,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        ∑ d : Fin 5, x.ofLp d * y.ofLp d
        from by rw [Finset.mul_sum]; congr 1; ext d; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b
    rw [show ∑ c : Fin 5,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * s =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s *
        ∑ c : Fin 5, x.ofLp c * y.ofLp c
        from by rw [Finset.mul_sum]; congr 1; ext c; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a
    rw [show ∑ b : Fin 5,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s * s =
        x.ofLp a * y.ofLp a * s * s *
        ∑ b : Fin 5, x.ofLp b * y.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
  simp_rw [← hs]
  rw [show ∑ a : Fin 5, x.ofLp a * y.ofLp a * s * s * s =
      (∑ a, x.ofLp a * y.ofLp a) * s * s * s from by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]]
  rw [← hs]; ring

-- ============================================================
-- ∑ BB = 54s² + 6 (= (6*5+24)s² + 6 for d=5)
-- ============================================================

private lemma sum_BB (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, B4 x p * B4 y p =
    54 * (@inner ℝ _ _ x y) ^ 2 + 6 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [B4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Rearrange Type A summands: x_i*x_j*y_i*y_j → (x_i*y_i)*(x_j*y_j)
  have ka : ∀ a b : Fin 5, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := fun a b => by ring
  have kb : ∀ a b : Fin 5, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := fun a b => by ring
  simp_rw [ka, kb]
  -- Factor ALL double sums (both standard and swapped variable order)
  simp_rw [factor2, factor2_swap]
  -- Substitute known values: inner product sums → s, norm sums → 1
  simp_rw [← hs]; rw [hxn, hyn]
  -- Collapse phantom sums under binders: ∑ b, const = 5 • const → 5 * const
  simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  -- Rearrange body so constant factor comes first
  simp_rw [show ∀ a : Fin 5, 5 * (x.ofLp a * y.ofLp a) * s =
      (5 * s) * (x.ofLp a * y.ofLp a) from fun a => by ring]
  -- Pull constant out of sum, substitute ∑(x·y) → s
  simp_rw [← Finset.mul_sum, ← hs]
  ring

-- ============================================================
-- ∑ BC = 42, ∑ CB = 42  (= 6*5 + 12 for d=5)
-- ============================================================

private lemma sum_BC (x : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1)
    (y : EuclideanSpace ℝ (Fin 5)) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, B4 x p * C4 y p = 42 := by
  have hxn := ofLp_norm_sq x hx
  simp only [B4, C4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [sum_ite_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Collapse: sum_const for constant sums, nsmul → mul, card → 5, hxn for ∑ x²
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, hxn]
  -- Factor ∑ 5*(x²) = 5*∑(x²) = 5*1 = 5
  simp_rw [← Finset.mul_sum, hxn]
  norm_num

private lemma sum_CB (x : EuclideanSpace ℝ (Fin 5)) (y : EuclideanSpace ℝ (Fin 5))
    (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, C4 x p * B4 y p = 42 := by
  simp_rw [show ∀ p, C4 x p * B4 y p = B4 y p * C4 x p from fun p => mul_comm _ _]
  exact sum_BC y hy x

-- ============================================================
-- phi4 and product decomposition
-- ============================================================

private def phi4 (x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  A4 x p - (1 : ℝ) / 9 * B4 x p + (1 : ℝ) / 63 * C4 x p

private lemma phi4_product (x y : EuclideanSpace ℝ (Fin 5))
    (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) :
    phi4 x p * phi4 y p =
    A4 x p * A4 y p
    - (1/9) * (A4 x p * B4 y p + B4 x p * A4 y p)
    + (1/63) * (A4 x p * C4 y p + C4 x p * A4 y p)
    + (1/81) * (B4 x p * B4 y p)
    - (1/567) * (B4 x p * C4 y p + C4 x p * B4 y p)
    + (1/3969) * (C4 x p * C4 y p) := by
  simp only [phi4]; ring

-- ============================================================
-- Main kernel identity
-- ============================================================

private lemma phi4_kernel (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, phi4 x p * phi4 y p =
    (8 : ℝ) / 21 * P5 4 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, phi4 x p * phi4 y p =
      (@inner ℝ _ _ x y) ^ 4 - 2 / 3 * (@inner ℝ _ _ x y) ^ 2 + 1 / 21 by
    rw [h, P5_4]; ring
  set s := @inner ℝ _ _ x y
  simp_rw [phi4_product]
  simp only [sub_eq_add_neg]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [sum_AA, sum_AB x y hx, sum_BA x y hy, sum_AC x y hx, sum_CA x y hy,
      sum_BB x y hx hy, sum_BC x hx y, sum_CB x y hy, sum_CC]
  ring

-- ============================================================
-- Public exports for use by PSD5.lean
-- ============================================================

/-- Feature map for k=4 in d=5: trace-free 4th moment tensor. -/
def phi4_d5_Feature (x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : ℝ :=
  phi4 x p

/-- Kernel identity for k=4 in d=5: ∑ φ₄(x)·φ₄(y) = (8/21)·P₅₄(⟪x,y⟫). -/
lemma phi4_d5_Feature_kernel (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5, phi4_d5_Feature x p * phi4_d5_Feature y p =
    (8 : ℝ) / 21 * P5 4 (@inner ℝ _ _ x y) := by
  simp only [phi4_d5_Feature]
  exact phi4_kernel x y hx hy

end
