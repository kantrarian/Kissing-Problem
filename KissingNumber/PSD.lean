import KissingNumber.Gegenbauer
import KissingNumber.PSD4CrossTerms
import KissingNumber.PSD5CrossTerms
import KissingNumber.PSD6CrossTerms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# PSD Property for Gegenbauer Sums

For unit vectors u₁,...,u_N on S⁷, we prove:
  ∀ k : Fin 7, k ≠ 0 → 0 ≤ ∑ᵢ ∑ⱼ P₈ k ⟪uᵢ, uⱼ⟫

This is the "positive semidefiniteness" condition needed for the Delsarte LP bound.
The proof uses feature maps (trace-free moment tensors) for each degree k.
-/

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

variable {N : ℕ} (u : Fin N → EuclideanSpace ℝ (Fin 8)) (hunit : ∀ i, ‖u i‖ = 1)

/-! ## Helpers for coordinate-level manipulation -/

/-- ‖x‖ = 1 implies ∑ (x.ofLp a)² = 1 -/
private lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

/-- Inner product = ∑ x.ofLp(a) * y.ofLp(a) -/
private lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]
  congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

/-! ## General Framework: PSD from Feature Map Kernel -/

/-- If φ is a feature map with kernel c · P_k, then ∑∑ P_k ≥ 0.
    The key identity: ∑_ij P_k(⟪uᵢ,uⱼ⟫) = c⁻¹ · ∑_p (∑_i φ(uᵢ)(p))² ≥ 0. -/
theorem psd_of_kernel {ι : Type*} [Fintype ι] {k : Fin 7} (c : ℝ) (hc : 0 < c)
    (φ : EuclideanSpace ℝ (Fin 8) → ι → ℝ)
    (hφ : ∀ x y : EuclideanSpace ℝ (Fin 8), ‖x‖ = 1 → ‖y‖ = 1 →
      ∑ p : ι, φ x p * φ y p = c * P8 k (@inner ℝ _ _ x y))
    (hunit' : ∀ i, ‖u i‖ = 1) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, P8 k (@inner ℝ _ _ (u i) (u j)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  suffices h : ∑ i : Fin N, ∑ j : Fin N, P8 k (@inner ℝ _ _ (u i) (u j)) =
      c⁻¹ * ∑ p : ι, (∑ i : Fin N, φ (u i) p) ^ 2 by
    rw [h]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hc)) (Finset.sum_nonneg fun p _ => sq_nonneg _)
  have h_rw : ∀ i j : Fin N, P8 k (@inner ℝ _ _ (u i) (u j)) =
      c⁻¹ * ∑ p : ι, φ (u i) p * φ (u j) p := by
    intro i j
    have hk := hφ (u i) (u j) (hunit' i) (hunit' j)
    field_simp [hcne]; linarith
  simp_rw [h_rw, ← Finset.mul_sum]
  congr 1
  simp_rw [show ∀ i : Fin N,
    ∑ j : Fin N, ∑ p : ι, φ (u i) p * φ (u j) p =
    ∑ p : ι, ∑ j : Fin N, φ (u i) p * φ (u j) p from fun _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1; ext p
  rw [sq, Finset.sum_mul]
  congr 1; ext i; rw [Finset.mul_sum]

/-! ## k = 1: ∑ᵢⱼ ⟪uᵢ,uⱼ⟫ = ‖∑ᵢ uᵢ‖² ≥ 0 -/

theorem P8_sum_nonneg_k1 :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, P8 1 (@inner ℝ _ _ (u i) (u j)) := by
  simp only [P8_1]
  have h : ∑ i : Fin N, ∑ j : Fin N, @inner ℝ _ _ (u i) (u j) =
      @inner ℝ _ _ (∑ i : Fin N, u i) (∑ j : Fin N, u j) := by
    rw [sum_inner]; congr 1; ext i; rw [inner_sum]
  rw [h, real_inner_self_eq_norm_sq]; exact sq_nonneg _

/-! ## k = 2: Feature map via trace-free 2-tensors -/

/-- Feature map for k=2: x ↦ (x(a)·x(b) - δ_{ab}/8) -/
private def phi2 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8) : ℝ :=
  x p.1 * x p.2 - if p.1 = p.2 then (1 : ℝ) / 8 else 0

/-- Kernel identity for k=2: ∑ φ₂(x)·φ₂(y) = (7/8)·P₂(⟪x,y⟫) -/
private lemma phi2_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8, phi2 x p * phi2 y p =
    (7 : ℝ) / 8 * P8 2 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 8 × Fin 8, phi2 x p * phi2 y p =
      (@inner ℝ _ _ x y) ^ 2 - 1 / 8 by rw [h, P8_2]; ring
  simp only [phi2]
  rw [Fintype.sum_prod_type]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hA : ∑ a : Fin 8, ∑ b : Fin 8,
      x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) = (@inner ℝ _ _ x y) ^ 2 := by
    rw [inner_ofLp, sq, Finset.sum_mul]
    congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext b; ring
  have hB : ∑ a : Fin 8, x.ofLp a * x.ofLp a * (1 / 8) = 1 / 8 := by
    rw [← Finset.sum_mul, ofLp_norm_sq x hx]; ring
  have hC : ∑ a : Fin 8, 1 / 8 * (y.ofLp a * y.ofLp a) = 1 / 8 := by
    rw [← Finset.mul_sum, ofLp_norm_sq y hy]; ring
  have hD : ∑ _a : Fin 8, (1 : ℝ) / 8 * (1 / 8) = 1 / 8 := by
    simp [Finset.sum_const, Fintype.card_fin]
  linarith

/-! ## k = 3: Feature map via trace-free 3-tensors -/

/-- Feature map for k=3: x ↦ x(a)x(b)x(c) - (1/10)(x(a)δ_{bc} + x(b)δ_{ac} + x(c)δ_{ab}) -/
private def phi3 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8 × Fin 8) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2
    - (1 : ℝ) / 10 * (x p.1 * (if p.2.1 = p.2.2 then 1 else 0)
      + x p.2.1 * (if p.1 = p.2.2 then 1 else 0)
      + x p.2.2 * (if p.1 = p.2.1 then 1 else 0))

/-- Kernel identity for k=3: ∑ φ₃(x)·φ₃(y) = (7/10)·P₃(⟪x,y⟫) -/
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
  -- Cubic: ∑∑∑ x(a)x(b)x(c)y(a)y(b)y(c) = s³
  have hCube : ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp c) = s ^ 3 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 8,
          x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp c) =
          x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * ∑ c : Fin 8, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 8, x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s =
          x.ofLp a * y.ofLp a * s * ∑ b : Fin 8, x.ofLp b * y.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [← hs]
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
  have h4s : ∑ a : Fin 8, 1 / 10 * (x.ofLp a * 1) * (1 / 10 * (y.ofLp a * 1)) =
      1 / 100 * s := by
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
  -- Combine everything
  linarith

/-! ## k = 4: Feature map via trace-free 4-tensors (proved in PSD4CrossTerms.lean) -/

/-! ## Combined PSD theorem -/

include hunit
/-- PSD for all k ≥ 1: the main theorem needed for the Delsarte bound. -/
theorem P8_sum_nonneg (k : Fin 7) (hk : k ≠ 0) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, P8 k (@inner ℝ _ _ (u i) (u j)) := by
  fin_cases k
  · exact absurd rfl hk
  · exact P8_sum_nonneg_k1 u
  · exact psd_of_kernel u (7 / 8) (by norm_num) phi2 phi2_kernel hunit
  · exact psd_of_kernel u (7 / 10) (by norm_num) phi3 phi3_kernel hunit
  · exact psd_of_kernel u (21 / 40) (by norm_num) phi4Feature phi4Feature_kernel hunit
  · exact psd_of_kernel u (3 / 8) (by norm_num) phi5Feature phi5Feature_kernel hunit
  · exact psd_of_kernel u (231 / 896) (by norm_num) phi6Feature phi6Feature_kernel hunit

end
