import KissingNumber.Gegenbauer5
import KissingNumber.PSD4_d5_CrossTerms
import KissingNumber.PSD5_d5_CrossTerms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# PSD Property for Gegenbauer Sums (Dimension 5)

For unit vectors u₁,...,u_N on S⁴ (in ℝ⁵), we prove:
  ∀ k : Fin 6, k ≠ 0 → 0 ≤ ∑ᵢ ∑ⱼ P₅ k ⟪uᵢ, uⱼ⟫

This is the "positive semidefiniteness" condition needed for the Delsarte LP bound.
The proof uses feature maps (trace-free moment tensors) for each degree k.

## Feature map constants for d=5:
- k=1: c = 1 (trivial: P₅₁(t) = t, Gram matrix is PSD)
- k=2: c = 4/5, φ₂(x)_{ab} = x_a x_b - δ_{ab}/5
- k=3: c = 4/7, φ₃(x)_{abc} = x_a x_b x_c - (1/7)(x_a δ_{bc} + x_b δ_{ac} + x_c δ_{ab})
- k=4: c = 8/21, φ₄(x)_{abcd} = x_a x_b x_c x_d - (1/9)B₄ + (1/63)C₄
- k=5: c = 8/33, φ₅(x)_{abcde} = x_a x_b x_c x_d x_e - (1/11)B₅ + (1/99)C₅
-/

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

variable {N : ℕ} (u : Fin N → EuclideanSpace ℝ (Fin 5)) (hunit : ∀ i, ‖u i‖ = 1)

/-! ## Helpers for coordinate-level manipulation (dimension 5) -/

/-- ‖x‖ = 1 implies ∑ (x a)² = 1 -/
private lemma ofLp_norm_sq_5 (x : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 5, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 5, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

/-- Inner product = ∑ x(a) * y(a) -/
private lemma inner_ofLp_5 (x y : EuclideanSpace ℝ (Fin 5)) :
    @inner ℝ _ _ x y = ∑ a : Fin 5, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]
  congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

/-! ## General Framework: PSD from Feature Map Kernel (dimension 5) -/

/-- If φ is a feature map with kernel c · P_k, then ∑∑ P_k ≥ 0. -/
theorem psd_of_kernel_5 {ι : Type*} [Fintype ι] {k : Fin 6} (c : ℝ) (hc : 0 < c)
    (φ : EuclideanSpace ℝ (Fin 5) → ι → ℝ)
    (hφ : ∀ x y : EuclideanSpace ℝ (Fin 5), ‖x‖ = 1 → ‖y‖ = 1 →
      ∑ p : ι, φ x p * φ y p = c * P5 k (@inner ℝ _ _ x y))
    (hunit' : ∀ i, ‖u i‖ = 1) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, P5 k (@inner ℝ _ _ (u i) (u j)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  suffices h : ∑ i : Fin N, ∑ j : Fin N, P5 k (@inner ℝ _ _ (u i) (u j)) =
      c⁻¹ * ∑ p : ι, (∑ i : Fin N, φ (u i) p) ^ 2 by
    rw [h]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hc)) (Finset.sum_nonneg fun p _ => sq_nonneg _)
  have h_rw : ∀ i j : Fin N, P5 k (@inner ℝ _ _ (u i) (u j)) =
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

theorem P5_sum_nonneg_k1 :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, P5 1 (@inner ℝ _ _ (u i) (u j)) := by
  simp only [P5_1]
  have h : ∑ i : Fin N, ∑ j : Fin N, @inner ℝ _ _ (u i) (u j) =
      @inner ℝ _ _ (∑ i : Fin N, u i) (∑ j : Fin N, u j) := by
    rw [sum_inner]; congr 1; ext i; rw [inner_sum]
  rw [h, real_inner_self_eq_norm_sq]; exact sq_nonneg _

/-! ## k = 2: Feature map via trace-free 2-tensors (d=5) -/

/-- Feature map for k=2 in d=5: x ↦ (x(a)·x(b) - δ_{ab}/5) -/
private def phi2_d5 (x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5) : ℝ :=
  x p.1 * x p.2 - if p.1 = p.2 then (1 : ℝ) / 5 else 0

/-- Kernel identity for k=2 in d=5: ∑ φ₂(x)·φ₂(y) = (4/5)·P₅₂(⟪x,y⟫) -/
private lemma phi2_d5_kernel (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5, phi2_d5 x p * phi2_d5 y p =
    (4 : ℝ) / 5 * P5 2 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 5 × Fin 5, phi2_d5 x p * phi2_d5 y p =
      (@inner ℝ _ _ x y) ^ 2 - 1 / 5 by rw [h, P5_2]; ring
  simp only [phi2_d5]
  rw [Fintype.sum_prod_type]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hA : ∑ a : Fin 5, ∑ b : Fin 5,
      x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) = (@inner ℝ _ _ x y) ^ 2 := by
    rw [inner_ofLp_5, sq, Finset.sum_mul]
    congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext b; ring
  have hB : ∑ a : Fin 5, x.ofLp a * x.ofLp a * (1 / 5) = 1 / 5 := by
    rw [← Finset.sum_mul, ofLp_norm_sq_5 x hx]; ring
  have hC : ∑ a : Fin 5, 1 / 5 * (y.ofLp a * y.ofLp a) = 1 / 5 := by
    rw [← Finset.mul_sum, ofLp_norm_sq_5 y hy]; ring
  have hD : ∑ _a : Fin 5, (1 : ℝ) / 5 * (1 / 5) = 1 / 5 := by
    simp [Finset.sum_const, Fintype.card_fin]
  linarith

/-! ## k = 3: Feature map via trace-free 3-tensors (d=5) -/

/-- Feature map for k=3 in d=5: x ↦ x(a)x(b)x(c) - (1/7)(x(a)δ_{bc} + x(b)δ_{ac} + x(c)δ_{ab}) -/
private def phi3_d5 (x : EuclideanSpace ℝ (Fin 5)) (p : Fin 5 × Fin 5 × Fin 5) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2
    - (1 : ℝ) / 7 * (x p.1 * (if p.2.1 = p.2.2 then 1 else 0)
      + x p.2.1 * (if p.1 = p.2.2 then 1 else 0)
      + x p.2.2 * (if p.1 = p.2.1 then 1 else 0))

/-- Kernel identity for k=3 in d=5: ∑ φ₃(x)·φ₃(y) = (4/7)·P₅₃(⟪x,y⟫) -/
private lemma phi3_d5_kernel (x y : EuclideanSpace ℝ (Fin 5)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 5 × Fin 5 × Fin 5, phi3_d5 x p * phi3_d5 y p =
    (4 : ℝ) / 7 * P5 3 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 5 × Fin 5 × Fin 5, phi3_d5 x p * phi3_d5 y p =
      (@inner ℝ _ _ x y) ^ 3 - 3 / 7 * @inner ℝ _ _ x y by
    rw [h, P5_3]; ring
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 5, x.ofLp a * y.ofLp a := inner_ofLp_5 x y
  have hxn := ofLp_norm_sq_5 x hx
  have hyn := ofLp_norm_sq_5 y hy
  simp only [phi3_d5]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [show ∀ (a b : Fin 5) (f : Fin 5 → ℝ),
      (∑ c : Fin 5, if a = b then f c else 0) = if a = b then ∑ c : Fin 5, f c else 0
      from fun a b f => by by_cases h : a = b <;> simp [h]]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Cubic term
  have hCube : ∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp c) = s ^ 3 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show ∑ c : Fin 5,
          x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp c) =
          x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * ∑ c : Fin 5, x.ofLp c * y.ofLp c
          from by rw [Finset.mul_sum]; congr 1; ext c; ring]
    simp_rw [← hs]
    conv_lhs =>
      arg 2; ext a
      rw [show ∑ b : Fin 5, x.ofLp a * y.ofLp a * (x.ofLp b * y.ofLp b) * s =
          x.ofLp a * y.ofLp a * s * ∑ b : Fin 5, x.ofLp b * y.ofLp b
          from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    simp_rw [← hs]
    rw [show ∑ a : Fin 5, x.ofLp a * y.ofLp a * s * s =
        (∑ a : Fin 5, x.ofLp a * y.ofLp a) * s * s from by
      rw [Finset.sum_mul, Finset.sum_mul]]
    rw [← hs]; ring
  -- Cross terms (cubic × linear)
  have h2a : ∑ a : Fin 5, ∑ b : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp b * (1 / 7 * (y.ofLp a * 1)) = 1 / 7 * s := by
    conv_rhs => rw [hs]; rw [Finset.mul_sum]
    congr 1; ext a
    rw [show ∑ b : Fin 5, x.ofLp a * x.ofLp b * x.ofLp b * (1 / 7 * (y.ofLp a * 1)) =
        1 / 7 * (x.ofLp a * y.ofLp a) * ∑ b : Fin 5, x.ofLp b * x.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    rw [hxn]; ring
  have h2b : ∑ a : Fin 5, ∑ b : Fin 5,
      x.ofLp a * x.ofLp b * x.ofLp a * (1 / 7 * (y.ofLp b * 1)) = 1 / 7 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 7 * ∑ a : Fin 5, x.ofLp a * y.ofLp a =
        (∑ a : Fin 5, x.ofLp a * x.ofLp a) * (1 / 7 * ∑ b : Fin 5, x.ofLp b * y.ofLp b)
        from by rw [hxn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext b; ring
  have h2c : ∑ a : Fin 5, ∑ c : Fin 5,
      x.ofLp a * x.ofLp a * x.ofLp c * (1 / 7 * (y.ofLp c * 1)) = 1 / 7 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 7 * ∑ c : Fin 5, x.ofLp c * y.ofLp c =
        (∑ a : Fin 5, x.ofLp a * x.ofLp a) * (1 / 7 * ∑ c : Fin 5, x.ofLp c * y.ofLp c)
        from by rw [hxn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext c; ring
  -- Cross terms (linear × cubic)
  have h3a : ∑ a : Fin 5, ∑ b : Fin 5,
      1 / 7 * (x.ofLp a * 1) * (y.ofLp a * y.ofLp b * y.ofLp b) = 1 / 7 * s := by
    conv_rhs => rw [hs]; rw [Finset.mul_sum]
    congr 1; ext a
    rw [show ∑ b : Fin 5, 1 / 7 * (x.ofLp a * 1) * (y.ofLp a * y.ofLp b * y.ofLp b) =
        1 / 7 * (x.ofLp a * y.ofLp a) * ∑ b : Fin 5, y.ofLp b * y.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
    rw [hyn]; ring
  have h3b : ∑ a : Fin 5, ∑ b : Fin 5,
      1 / 7 * (x.ofLp b * 1) * (y.ofLp a * y.ofLp b * y.ofLp a) = 1 / 7 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 7 * ∑ b : Fin 5, x.ofLp b * y.ofLp b =
        (∑ a : Fin 5, y.ofLp a * y.ofLp a) * (1 / 7 * ∑ b : Fin 5, x.ofLp b * y.ofLp b)
        from by rw [hyn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext b; ring
  have h3c : ∑ a : Fin 5, ∑ c : Fin 5,
      1 / 7 * (x.ofLp c * 1) * (y.ofLp a * y.ofLp a * y.ofLp c) = 1 / 7 * s := by
    conv_rhs => rw [hs]
    rw [show 1 / 7 * ∑ c : Fin 5, x.ofLp c * y.ofLp c =
        (∑ a : Fin 5, y.ofLp a * y.ofLp a) * (1 / 7 * ∑ c : Fin 5, x.ofLp c * y.ofLp c)
        from by rw [hyn]; ring]
    rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext a
    rw [Finset.mul_sum]; congr 1; ext c; ring
  -- Delta×delta terms
  have h4s : ∑ a : Fin 5, 1 / 7 * (x.ofLp a * 1) * (1 / 7 * (y.ofLp a * 1)) =
      1 / 49 * s := by
    conv_rhs => rw [hs]; rw [Finset.mul_sum]
    congr 1; ext a; ring
  have h4d_a : ∑ a : Fin 5, ∑ b : Fin 5,
      1 / 7 * (x.ofLp a * 1) * (1 / 7 * (y.ofLp a * 1)) = 5 / 49 * s := by
    simp_rw [show ∀ a : Fin 5, ∑ _b : Fin 5,
        1 / 7 * (x.ofLp a * 1) * (1 / 7 * (y.ofLp a * 1)) =
        5 * (1 / 7 * (x.ofLp a * 1) * (1 / 7 * (y.ofLp a * 1)))
        from fun a => by simp [Finset.sum_const, Fintype.card_fin]]
    rw [← Finset.mul_sum, h4s]; ring
  have h4d_b : ∑ a : Fin 5, ∑ b : Fin 5,
      1 / 7 * (x.ofLp b * 1) * (1 / 7 * (y.ofLp b * 1)) = 5 / 49 * s := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ b : Fin 5, ∑ _a : Fin 5,
        1 / 7 * (x.ofLp b * 1) * (1 / 7 * (y.ofLp b * 1)) =
        5 * (1 / 7 * (x.ofLp b * 1) * (1 / 7 * (y.ofLp b * 1)))
        from fun b => by simp [Finset.sum_const, Fintype.card_fin]]
    rw [← Finset.mul_sum, h4s]; ring
  -- Combine
  linarith

/-! ## Combined PSD theorem for dimension 5 -/

include hunit
/-- PSD for all k ≥ 1 in dimension 5: the main theorem needed for the Delsarte bound.
    All cases proved via feature maps (trace-free moment tensors). -/
theorem P5_sum_nonneg (k : Fin 6) (hk : k ≠ 0) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, P5 k (@inner ℝ _ _ (u i) (u j)) := by
  fin_cases k
  · exact absurd rfl hk
  · exact P5_sum_nonneg_k1 u
  · exact psd_of_kernel_5 u (4 / 5) (by norm_num) phi2_d5 phi2_d5_kernel hunit
  · exact psd_of_kernel_5 u (4 / 7) (by norm_num) phi3_d5 phi3_d5_kernel hunit
  · exact psd_of_kernel_5 u (8 / 21) (by norm_num) phi4_d5_Feature phi4_d5_Feature_kernel hunit
  · exact psd_of_kernel_5 u (8 / 33) (by norm_num) phi5_d5_Feature phi5_d5_Feature_kernel hunit

end
