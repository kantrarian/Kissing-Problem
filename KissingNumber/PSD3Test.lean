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

private def phi3 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8 × Fin 8) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2
    - (1 : ℝ) / 10 * (x p.1 * (if p.2.1 = p.2.2 then 1 else 0)
      + x p.2.1 * (if p.1 = p.2.2 then 1 else 0)
      + x p.2.2 * (if p.1 = p.2.1 then 1 else 0))

private lemma phi3_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8 × Fin 8, phi3 x p * phi3 y p =
    (7 : ℝ) / 10 * P8 3 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 8 × Fin 8 × Fin 8, phi3 x p * phi3 y p =
      (@inner ℝ _ _ x y) ^ 3 - 3 / 10 * @inner ℝ _ _ x y by
    rw [h, P8_3]; ring
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  -- Expand and collapse deltas
  simp only [phi3]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Round 2: pull constant-condition ifs out, re-collapse
  simp_rw [show ∀ (a b : Fin 8) (f : Fin 8 → ℝ),
      (∑ c : Fin 8, if a = b then f c else 0) = if a = b then ∑ c : Fin 8, f c else 0
      from fun a b f => by by_cases h : a = b <;> simp [h]]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Now all deltas are collapsed. Prove each sum component.
  -- Cubic: ∑∑∑ x(a)x(b)x(c)y(a)y(b)y(c) = s³
  have hCube : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp c) = s ^ 3 := by
    -- Factor: x(a)x(b)x(c)y(a)y(b)y(c) = (x(a)y(a))(x(b)y(b)) · (x(c)y(c))
    -- Factor c-sum
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8,
          x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp c) =
          x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    -- Factor b-sum
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 8, x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s =
          x.ofLp a * y.ofLp a * s * ∑ b : Fin 8, x.ofLp b * y.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [← hs]
    -- Factor a-sum
    rw [show ∑ a : Fin 8, x.ofLp a * y.ofLp a * s * s =
        (∑ a : Fin 8, x.ofLp a * y.ofLp a) * s * s from by
      rw [Finset.sum_mul, Finset.sum_mul]]
    rw [← hs]; ring
  -- Cross term: ∑_a ∑_b x(a)x(b)²y(a)*(1/10) = s/10
  have h2a : ∑ a : Fin 8, ∑ b : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp b * (1 / 10 * (y.ofLp a * 1)) = 1 / 10 * s := by
    conv_rhs => rw [hs]; rw [Finset.mul_sum]
    congr 1; ext a
    rw [show ∑ b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * (1 / 10 * (y.ofLp a * 1)) =
        1 / 10 * (x.ofLp a * y.ofLp a) * ∑ b : Fin 8, x.ofLp b * x.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    rw [hxn]; ring
  -- Cross term: ∑_a ∑_b x(a)x(b)x(a)y(b)*(1/10) = s/10
  have h2b : ∑ a : Fin 8, ∑ b : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp a * (1 / 10 * (y.ofLp b * 1)) = 1 / 10 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 10 * ∑ a : Fin 8, x.ofLp a * y.ofLp a =
        (∑ a : Fin 8, x.ofLp a * x.ofLp a) * (1 / 10 * ∑ b : Fin 8, x.ofLp b * y.ofLp b)
        from by rw [hxn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext b; ring
  -- Cross term: ∑_a ∑_c x(a)²x(c)y(c)*(1/10) = s/10
  have h2c : ∑ a : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp a * x.ofLp c * (1 / 10 * (y.ofLp c * 1)) = 1 / 10 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 10 * ∑ c : Fin 8, x.ofLp c * y.ofLp c =
        (∑ a : Fin 8, x.ofLp a * x.ofLp a) * (1 / 10 * ∑ c : Fin 8, x.ofLp c * y.ofLp c)
        from by rw [hxn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext c; ring
  -- Cross term: ∑_a ∑_b (1/10)x(a)y(a)y(b)² = s/10
  have h3a : ∑ a : Fin 8, ∑ b : Fin 8,
      1 / 10 * (x.ofLp a * 1) * (y.ofLp a * y.ofLp b * y.ofLp b) = 1 / 10 * s := by
    conv_rhs => rw [hs]; rw [Finset.mul_sum]
    congr 1; ext a
    rw [show ∑ b : Fin 8, 1 / 10 * (x.ofLp a * 1) * (y.ofLp a * y.ofLp b * y.ofLp b) =
        1 / 10 * (x.ofLp a * y.ofLp a) * ∑ b : Fin 8, y.ofLp b * y.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    rw [hyn]; ring
  -- Cross term: ∑_a ∑_b (1/10)x(b)y(a)y(b)y(a) = s/10
  have h3b : ∑ a : Fin 8, ∑ b : Fin 8,
      1 / 10 * (x.ofLp b * 1) * (y.ofLp a * y.ofLp b * y.ofLp a) = 1 / 10 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 10 * ∑ b : Fin 8, x.ofLp b * y.ofLp b =
        (∑ a : Fin 8, y.ofLp a * y.ofLp a) * (1 / 10 * ∑ b : Fin 8, x.ofLp b * y.ofLp b)
        from by rw [hyn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext b; ring
  -- Cross term: ∑_a ∑_c (1/10)x(c)y(a)²y(c) = s/10
  have h3c : ∑ a : Fin 8, ∑ c : Fin 8,
      1 / 10 * (x.ofLp c * 1) * (y.ofLp a * y.ofLp a * y.ofLp c) = 1 / 10 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 10 * ∑ c : Fin 8, x.ofLp c * y.ofLp c =
        (∑ a : Fin 8, y.ofLp a * y.ofLp a) * (1 / 10 * ∑ c : Fin 8, x.ofLp c * y.ofLp c)
        from by rw [hyn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext c; ring
  -- 1-sum delta×delta: ∑_a (1/100)x(a)y(a) = s/100
  have h4s : ∑ a : Fin 8, 1 / 10 * (x.ofLp a * 1) * (1 / 10 * (y.ofLp a * 1)) = 1 / 100 * s := by
    conv_rhs => rw [hs]; rw [Finset.mul_sum]
    congr 1; ext a; ring
  -- 2-sum delta×delta (inner doesn't depend on outer): 8*(s/100)
  have h4d_a : ∑ a : Fin 8, ∑ b : Fin 8,
      1 / 10 * (x.ofLp a * 1) * (1 / 10 * (y.ofLp a * 1)) = 8 / 100 * s := by
    simp_rw [show ∀ a : Fin 8, ∑ _b : Fin 8,
        1 / 10 * (x.ofLp a * 1) * (1 / 10 * (y.ofLp a * 1)) =
        8 * (1 / 10 * (x.ofLp a * 1) * (1 / 10 * (y.ofLp a * 1)))
        from fun a => by simp [Finset.sum_const, Fintype.card_fin]]
    rw [← Finset.mul_sum, h4s]; ring
  -- 2-sum delta×delta (inner depends on inner variable): 8*(s/100)
  have h4d_b : ∑ a : Fin 8, ∑ b : Fin 8,
      1 / 10 * (x.ofLp b * 1) * (1 / 10 * (y.ofLp b * 1)) = 8 / 100 * s := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ b : Fin 8, ∑ _a : Fin 8,
        1 / 10 * (x.ofLp b * 1) * (1 / 10 * (y.ofLp b * 1)) =
        8 * (1 / 10 * (x.ofLp b * 1) * (1 / 10 * (y.ofLp b * 1)))
        from fun b => by simp [Finset.sum_const, Fintype.card_fin]]
    rw [← Finset.mul_sum, h4s]; ring
  -- Combine everything with linarith
  linarith

end
