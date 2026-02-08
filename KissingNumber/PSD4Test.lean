import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

private lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

private lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]
  congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

-- Decompose phi4 into three parts: A (monomial), B (delta-trace), C (double-delta)
private def A4 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8 × Fin 8 × Fin 8) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2.1 * x p.2.2.2

private def B4 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8 × Fin 8 × Fin 8) : ℝ :=
    x p.1 * x p.2.1 * (if p.2.2.1 = p.2.2.2 then 1 else 0)
  + x p.1 * x p.2.2.1 * (if p.2.1 = p.2.2.2 then 1 else 0)
  + x p.1 * x p.2.2.2 * (if p.2.1 = p.2.2.1 then 1 else 0)
  + x p.2.1 * x p.2.2.1 * (if p.1 = p.2.2.2 then 1 else 0)
  + x p.2.1 * x p.2.2.2 * (if p.1 = p.2.2.1 then 1 else 0)
  + x p.2.2.1 * x p.2.2.2 * (if p.1 = p.2.1 then 1 else 0)

private def C4 (_x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8 × Fin 8 × Fin 8) : ℝ :=
    (if p.1 = p.2.1 then 1 else 0) * (if p.2.2.1 = p.2.2.2 then 1 else 0)
  + (if p.1 = p.2.2.1 then 1 else 0) * (if p.2.1 = p.2.2.2 then 1 else 0)
  + (if p.1 = p.2.2.2 then 1 else 0) * (if p.2.1 = p.2.2.1 then 1 else 0)

private def phi4 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8 × Fin 8 × Fin 8) : ℝ :=
  A4 x p - (1 : ℝ) / 12 * B4 x p + (1 : ℝ) / 120 * C4 x p

-- Product decomposition
private lemma phi4_product (x y : EuclideanSpace ℝ (Fin 8))
    (p : Fin 8 × Fin 8 × Fin 8 × Fin 8) :
    phi4 x p * phi4 y p =
    A4 x p * A4 y p
    - (1/12) * (A4 x p * B4 y p + B4 x p * A4 y p)
    + (1/120) * (A4 x p * C4 y p + C4 x p * A4 y p)
    + (1/144) * (B4 x p * B4 y p)
    - (1/1440) * (B4 x p * C4 y p + C4 x p * B4 y p)
    + (1/14400) * (C4 x p * C4 y p) := by
  simp only [phi4]; ring

-- ∑ AA = s⁴
private lemma sum_AA (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, A4 x p * A4 y p =
    (@inner ℝ _ _ x y) ^ 4 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [A4]
  simp_rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c
    rw [show ∑ d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        ∑ d : Fin 8, x.ofLp d * y.ofLp d
        from by rw [Finset.mul_sum]; congr 1; ext d; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b
    rw [show ∑ c : Fin 8,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * s =
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s *
        ∑ c : Fin 8, x.ofLp c * y.ofLp c
        from by rw [Finset.mul_sum]; congr 1; ext c; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a
    rw [show ∑ b : Fin 8,
        x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s * s =
        x.ofLp a * y.ofLp a * s * s *
        ∑ b : Fin 8, x.ofLp b * y.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
  simp_rw [← hs]
  rw [show ∑ a : Fin 8, x.ofLp a * y.ofLp a * s * s * s =
      (∑ a : Fin 8, x.ofLp a * y.ofLp a) * s * s * s from by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]]
  rw [← hs]; ring

-- Helper: ∑_a f(a) * (∑_b g(b)) = (∑_a f(a)) * (∑_b g(b))
-- (This is just Finset.sum_mul with the right form)

-- ∑ AB = 6s² (for unit x)
private lemma sum_AB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, A4 x p * B4 y p =
    6 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A4, B4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Round 2: collapse remaining ifs
  simp_rw [show ∀ (a b : Fin 8) (f : Fin 8 → ℝ),
      (∑ c : Fin 8, if a = b then f c else 0) = if a = b then ∑ c : Fin 8, f c else 0
      from fun a b f => by by_cases h : a = b <;> simp [h]]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Goal: 6 triple sums, each = s^2.
  -- T1: ∑_a ∑_b ∑_c x(a)x(b)x(c)x(c)*y(a)y(b) [c squared in x]
  have h1 : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * (y.ofLp a * y.ofLp b) = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * (y.ofLp a * y.ofLp b) =
          x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * ∑ c : Fin 8, x.ofLp c * x.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [hxn, mul_one]
    rw [show ∑ a : Fin 8, ∑ b : Fin 8, x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) =
        (∑ a, x.ofLp a * y.ofLp a) * ∑ b, x.ofLp b * y.ofLp b from by
      rw [Finset.sum_mul]; congr 1; ext a; rw [Finset.mul_sum]]
    rw [← hs]; ring
  -- T2: ∑_a ∑_b ∑_c x(a)x(b)x(c)x(b)*y(a)y(c) [b squared in x]
  have h2 : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp c) = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp c) =
          x.ofLp a * y.ofLp a * (x.ofLp b * x.ofLp b) * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 8, x.ofLp a * y.ofLp a * (x.ofLp b * x.ofLp b) * s =
          x.ofLp a * y.ofLp a * s * ∑ b : Fin 8, x.ofLp b * x.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [hxn, mul_one]
    rw [show ∑ a : Fin 8, x.ofLp a * y.ofLp a * s =
        (∑ a, x.ofLp a * y.ofLp a) * s from by rw [Finset.sum_mul]]
    rw [← hs]; ring
  -- T3: ∑_a ∑_b ∑_c x(a)x(b)x(b)x(c)*y(a)y(c) [b squared in x]
  have h3 : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp c) = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp c) =
          x.ofLp a * y.ofLp a * (x.ofLp b * x.ofLp b) * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 8, x.ofLp a * y.ofLp a * (x.ofLp b * x.ofLp b) * s =
          x.ofLp a * y.ofLp a * s * ∑ b : Fin 8, x.ofLp b * x.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [hxn, mul_one]
    rw [show ∑ a : Fin 8, x.ofLp a * y.ofLp a * s =
        (∑ a, x.ofLp a * y.ofLp a) * s from by rw [Finset.sum_mul]]
    rw [← hs]; ring
  -- T4: ∑_a ∑_b ∑_c x(a)x(b)x(c)x(a)*y(b)y(c) [a squared in x]
  have h4 : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp c) = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp c) =
          x.ofLp a * x.ofLp a * (x.ofLp b * y.ofLp b) * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 8, x.ofLp a * x.ofLp a * (x.ofLp b * y.ofLp b) * s =
          x.ofLp a * x.ofLp a * s * ∑ b : Fin 8, x.ofLp b * y.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [← hs]
    rw [show ∑ a : Fin 8, x.ofLp a * x.ofLp a * s * s =
        (∑ a, x.ofLp a * x.ofLp a) * s * s from by rw [Finset.sum_mul, Finset.sum_mul]]
    rw [hxn]; ring
  -- T5: ∑_a ∑_b ∑_c x(a)x(b)x(a)x(c)*y(b)y(c) [a squared in x]
  have h5 : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp c) = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp c) =
          x.ofLp a * x.ofLp a * (x.ofLp b * y.ofLp b) * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 8, x.ofLp a * x.ofLp a * (x.ofLp b * y.ofLp b) * s =
          x.ofLp a * x.ofLp a * s * ∑ b : Fin 8, x.ofLp b * y.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [← hs]
    rw [show ∑ a : Fin 8, x.ofLp a * x.ofLp a * s * s =
        (∑ a, x.ofLp a * x.ofLp a) * s * s from by rw [Finset.sum_mul, Finset.sum_mul]]
    rw [hxn]; ring
  -- T6: ∑_a ∑_c ∑_c1 x(a)x(a)x(c)x(c1)*y(c)y(c1) [a squared in x]
  have h6 : ∑ a : Fin 8, ∑ c : Fin 8, ∑ c1 : Fin 8,
      x.ofLp a * x.ofLp a * x.ofLp c * x.ofLp c1 * (y.ofLp c * y.ofLp c1) = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext c
      rw [show ∑ c1 : Fin 8, x.ofLp a * x.ofLp a * x.ofLp c * x.ofLp c1 * (y.ofLp c * y.ofLp c1) =
          x.ofLp a * x.ofLp a * (x.ofLp c * y.ofLp c) * ∑ c1 : Fin 8, x.ofLp c1 * y.ofLp c1
          from by rw [Finset.mul_sum]; congr 1; ext c1; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ c : Fin 8, x.ofLp a * x.ofLp a * (x.ofLp c * y.ofLp c) * s =
          x.ofLp a * x.ofLp a * s * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    rw [show ∑ a : Fin 8, x.ofLp a * x.ofLp a * s * s =
        (∑ a, x.ofLp a * x.ofLp a) * s * s from by rw [Finset.sum_mul, Finset.sum_mul]]
    rw [hxn]; ring
  linarith

-- ∑ BA = 6s² (for unit y, symmetric to AB)
private lemma sum_BA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, B4 x p * A4 y p =
    6 * (@inner ℝ _ _ x y) ^ 2 := by
  sorry

-- ∑ AC = 3 (for unit x, C doesn't depend on y)
private lemma sum_AC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, A4 x p * C4 y p = 3 := by
  have hxn := ofLp_norm_sq x hx
  simp only [A4, C4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Goal has 3 terms. Need to factor them as (∑ x²)² = 1² = 1 each.
  -- Term 1: ∑_{x1,x2,x3} if x1=x2 then x(x1)*x(x2)*x(x3)² else 0
  --   Swap x_2 and x_3 sums, then collapse if
  -- Term 2: ∑_{x1,x2} x(x1)*x(x2)*x(x1)*x(x2) = ∑_{x1,x2} (x(x1)*x(x2))²
  -- Term 3: ∑_{x1..x4} if x2=x3 then if x1=x4 then x(x1)*x(x2)*x(x3)*x(x4) else 0 else 0
  --   Swap inner sums, then collapse ifs
  -- Use Finset.sum_comm on the inner sums of terms 1 and 3
  conv_lhs =>
    -- Term 1: swap ∑ x_2 and ∑ x_3 so if x_1 = x_2 is innermost
    arg 1; arg 1
    arg 2; ext x_1
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Term 3 still has nested ifs: swap ∑ x_3 past ∑ x_4 so x_3 is innermost
  conv_lhs =>
    arg 2
    arg 2; ext x_1; arg 2; ext x_2
    rw [Finset.sum_comm]
  -- Now inner sum is ∑ x_3, if x_2 = x_3 then ... else 0
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- All 3 sums have summand x(a)²*x(b)² (up to ring). Normalize summands.
  have h1 : ∀ a b : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b = x.ofLp a * x.ofLp a * (x.ofLp b * x.ofLp b) := by
    intros; ring
  have h2 : ∀ a b : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a = x.ofLp a * x.ofLp a * (x.ofLp b * x.ofLp b) := by
    intros; ring
  simp_rw [h1, h2]
  -- Also normalize term 1
  have h0 : ∀ a b : Fin 8,
      x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b = x.ofLp a * x.ofLp a * (x.ofLp b * x.ofLp b) := by
    intros; ring
  simp_rw [h0]
  -- Now all 3 sums are ∑_a ∑_b x(a)²*x(b)²
  -- Factor: ∑_a ∑_b x(a)²*x(b)² = (∑_a x(a)²) * (∑_b x(b)²)
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, hxn]
  norm_num

-- ∑ CA = 3 (symmetric)
private lemma sum_CA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, C4 x p * A4 y p = 3 := by
  sorry

-- ∑ BB = 72s² + 6 (for unit x,y)
private lemma sum_BB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, B4 x p * B4 y p =
    72 * (@inner ℝ _ _ x y) ^ 2 + 6 := by
  sorry

-- ∑ BC = 60 (for unit x)
private lemma sum_BC (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, B4 x p * C4 y p = 60 := by
  sorry

-- ∑ CB = 60 (for unit y)
private lemma sum_CB (x : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, C4 x p * B4 y p = 60 := by
  sorry

-- ∑ CC = 240
private lemma sum_CC (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, C4 x p * C4 y p = 240 := by
  simp only [C4]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const]
  norm_num

-- Main kernel identity
private lemma phi4_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, phi4 x p * phi4 y p =
    (21 : ℝ) / 40 * P8 4 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 8 × Fin 8 × Fin 8 × Fin 8, phi4 x p * phi4 y p =
      (@inner ℝ _ _ x y) ^ 4 - 1 / 2 * (@inner ℝ _ _ x y) ^ 2 + 1 / 40 by
    rw [h, P8_4]; ring
  set s := @inner ℝ _ _ x y
  -- Expand using product decomposition
  simp_rw [phi4_product]
  -- Split sums
  simp only [sub_eq_add_neg]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- Substitute cross-term values
  rw [sum_AA, sum_AB x y hx, sum_BA x y hy, sum_AC x y hx, sum_CA x y hy,
      sum_BB x y hx hy, sum_BC x hx y, sum_CB x y hy, sum_CC]
  ring

end
