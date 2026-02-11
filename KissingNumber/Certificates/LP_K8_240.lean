import KissingNumber.Delsarte
import KissingNumber.K
import KissingNumber.Witness.E8
import KissingNumber.PSD
import Mathlib.Tactic

/-!
# Delsarte LP Certificate for K(8) = 240

This file defines the certificate polynomial g(t) = (t+1)(t+1/2)²t²(t-1/2)
and verifies all conditions needed to apply the Delsarte bound.

## Certificate properties:
1. g(t) ≤ 0 on [-1, 1/2] — from its factored form
2. g(1) = 9/4
3. Gegenbauer coefficients c₀,...,c₆ are all positive
4. g(1)/c₀ = 240

Combined with the lower bound K(8) ≥ 240 from the E8 witness,
this yields K(8) = 240.
-/

open scoped BigOperators RealInnerProductSpace
open Real KissingNumber

noncomputable section

/-! ## Certificate polynomial and its Gegenbauer coefficients -/

/-- The Delsarte certificate polynomial for dimension 8:
    g(t) = (t+1)(t+1/2)²t²(t-1/2)
    Expanded: t⁶ + (3/2)t⁵ + (1/4)t⁴ - (3/8)t³ - (1/8)t² -/
def e8_cert (t : ℝ) : ℝ :=
  (t + 1) * (t + 1/2)^2 * t^2 * (t - 1/2)

/-- Gegenbauer coefficients of the certificate polynomial. -/
def e8_coeff : Fin 7 → ℝ
  | ⟨0, _⟩ => 3/320
  | ⟨1, _⟩ => 3/40
  | ⟨2, _⟩ => 15/64
  | ⟨3, _⟩ => 39/80
  | ⟨4, _⟩ => 399/640
  | ⟨5, _⟩ => 9/16
  | ⟨6, _⟩ => 231/896

@[simp] lemma e8_coeff_0 : e8_coeff 0 = 3/320 := rfl
@[simp] lemma e8_coeff_1 : e8_coeff 1 = 3/40 := rfl
@[simp] lemma e8_coeff_2 : e8_coeff 2 = 15/64 := rfl
@[simp] lemma e8_coeff_3 : e8_coeff 3 = 39/80 := rfl
@[simp] lemma e8_coeff_4 : e8_coeff 4 = 399/640 := rfl
@[simp] lemma e8_coeff_5 : e8_coeff 5 = 9/16 := rfl
@[simp] lemma e8_coeff_6 : e8_coeff 6 = 231/896 := rfl

/-! ## Certificate verification -/

/-- The certificate polynomial equals its Gegenbauer expansion. -/
theorem e8_expansion : ∀ t : ℝ, e8_cert t = ∑ k : Fin 7, e8_coeff k * P8 k t := by
  intro t
  simp only [e8_cert, e8_coeff, P8]
  simp only [Fin.sum_univ_seven]
  ring

/-- All Gegenbauer coefficients c_k for k ≥ 1 are nonneg. -/
theorem e8_coeff_pos : ∀ k : Fin 7, k ≠ 0 → 0 ≤ e8_coeff k := by
  intro k hk
  fin_cases k <;> simp_all [e8_coeff] <;> norm_num

/-- c₀ > 0. -/
theorem e8_coeff_zero_pos : 0 < e8_coeff 0 := by
  simp [e8_coeff]

/-- g(t) ≤ 0 for t ∈ [-1, 1/2].
    Proof: g(t) = (t+1)(t+1/2)²t²(t-1/2).
    For t ∈ [-1, 1/2]: (t+1) ≥ 0, (t+1/2)² ≥ 0, t² ≥ 0, (t-1/2) ≤ 0.
    Product of nonneg × nonneg × nonneg × nonpos ≤ 0. -/
theorem e8_cert_nonpos : ∀ t, t ∈ Set.Icc (-1 : ℝ) (1/2) → e8_cert t ≤ 0 := by
  intro t ⟨ht_lb, ht_ub⟩
  unfold e8_cert
  have h1 : 0 ≤ t + 1 := by linarith
  have h2 : 0 ≤ (t + 1/2) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ t ^ 2 := sq_nonneg _
  have h4 : t - 1/2 ≤ 0 := by linarith
  have h12 : 0 ≤ (t + 1) * (t + 1/2) ^ 2 := mul_nonneg h1 h2
  have h123 : 0 ≤ (t + 1) * (t + 1/2) ^ 2 * t ^ 2 := mul_nonneg h12 h3
  exact mul_nonpos_of_nonneg_of_nonpos h123 h4

/-- g(1) = c₀ · 240. -/
theorem e8_bound_value : e8_cert 1 = e8_coeff 0 * 240 := by
  simp [e8_cert, e8_coeff]; ring

/-! ## Main upper bound theorem -/

/-- The kissing number in dimension 8 is at most 240.

    This uses the Delsarte LP bound with the E8 certificate polynomial.
    The PSD property is proved via feature map kernel identities in PSD.lean. -/
theorem K8_le_240 : K 8 ≤ 240 := by
  apply sSup_le
  intro x hx
  obtain ⟨N, hN, rfl⟩ := hx
  obtain ⟨X, hX⟩ := hN
  obtain ⟨u, hunit, hinner⟩ := kissing_to_unit_sphere hX
  have h_le : N ≤ 240 := delsarte_bound_8
    e8_cert e8_coeff e8_expansion e8_coeff_pos e8_coeff_zero_pos
    e8_cert_nonpos e8_bound_value N u hunit hinner
    (fun k hk => P8_sum_nonneg u hunit k hk)
  exact WithTop.coe_le_coe.mpr h_le

/-- The lower bound K(8) ≥ 240 from the E8 root system. -/
private theorem two_forty_le_K8 : (240 : WithTop ℕ) ≤ K 8 :=
  le_K_of_exists exists_kissing_240

/-- The kissing number in dimension 8 is exactly 240. -/
theorem K8_eq_240 : K 8 = 240 :=
  le_antisymm K8_le_240 two_forty_le_K8

end
