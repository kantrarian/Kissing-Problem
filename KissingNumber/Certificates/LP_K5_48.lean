import KissingNumber.Delsarte5
import KissingNumber.K
import KissingNumber.D5
import KissingNumber.PSD5
import Mathlib.Tactic

/-!
# Delsarte LP Certificate for K(5) ≤ 48

This file defines the certificate polynomial f(t) = (t+5/7)²(t+1/7)²(t-1/2)
and verifies all conditions needed to apply the Delsarte bound for dimension 5.

## Certificate properties:
1. f(t) ≤ 0 on [-1, 1/2] — from its factored form:
   (t+5/7)² ≥ 0, (t+1/7)² ≥ 0, (t-1/2) ≤ 0 on [-1, 1/2]
2. f(1) = 4608/2401
3. Gegenbauer coefficients c₀,...,c₅ are all positive:
   c₀ = 96/2401, c₁ = 1412/7203, c₂ = 424/1029,
   c₃ = 2136/3773, c₄ = 68/147, c₅ = 8/33
4. f(1)/c₀ = (4608/2401)/(96/2401) = 48

Combined with the lower bound K(5) ≥ 40 from the D5 witness,
this yields 40 ≤ K(5) ≤ 48.
-/

open scoped BigOperators RealInnerProductSpace
open Real KissingNumber

noncomputable section

/-! ## Certificate polynomial and its Gegenbauer coefficients -/

/-- The Delsarte certificate polynomial for dimension 5:
    f(t) = (t + 5/7)² · (t + 1/7)² · (t - 1/2)
    Roots: t = -5/7 (double), t = -1/7 (double), t = 1/2 (simple).
    Standard form: t⁵ + 17/14·t⁴ + 4/49·t³ - 101/343·t² - 185/2401·t - 25/4802 -/
def k5_cert (t : ℝ) : ℝ :=
  (t + 5 / 7) ^ 2 * (t + 1 / 7) ^ 2 * (t - 1 / 2)

/-- Gegenbauer coefficients of the K(5) certificate polynomial.
    Computed via exact rational Gaussian elimination. -/
def k5_coeff : Fin 6 → ℝ
  | ⟨0, _⟩ => 96 / 2401
  | ⟨1, _⟩ => 1412 / 7203
  | ⟨2, _⟩ => 424 / 1029
  | ⟨3, _⟩ => 2136 / 3773
  | ⟨4, _⟩ => 68 / 147
  | ⟨5, _⟩ => 8 / 33

@[simp] lemma k5_coeff_0 : k5_coeff 0 = 96 / 2401 := rfl
@[simp] lemma k5_coeff_1 : k5_coeff 1 = 1412 / 7203 := rfl
@[simp] lemma k5_coeff_2 : k5_coeff 2 = 424 / 1029 := rfl
@[simp] lemma k5_coeff_3 : k5_coeff 3 = 2136 / 3773 := rfl
@[simp] lemma k5_coeff_4 : k5_coeff 4 = 68 / 147 := rfl
@[simp] lemma k5_coeff_5 : k5_coeff 5 = 8 / 33 := rfl

/-! ## Certificate verification -/

/-- The certificate polynomial equals its Gegenbauer expansion.
    f(t) = ∑ₖ cₖ · P₅ₖ(t) -/
theorem k5_expansion : ∀ t : ℝ, k5_cert t = ∑ k : Fin 6, k5_coeff k * P5 k t := by
  intro t
  simp only [k5_cert, k5_coeff, P5]
  simp only [Fin.sum_univ_six]
  ring

/-- All Gegenbauer coefficients c_k for k ≥ 1 are nonneg. -/
theorem k5_coeff_pos : ∀ k : Fin 6, k ≠ 0 → 0 ≤ k5_coeff k := by
  intro k hk
  fin_cases k <;> simp_all [k5_coeff] <;> norm_num

/-- c₀ > 0. -/
theorem k5_coeff_zero_pos : 0 < k5_coeff 0 := by
  simp [k5_coeff]; norm_num

/-- f(t) ≤ 0 for t ∈ [-1, 1/2].
    Proof: f(t) = (t+5/7)²·(t+1/7)²·(t-1/2).
    For t ∈ [-1, 1/2]: (t+5/7)² ≥ 0, (t+1/7)² ≥ 0, (t-1/2) ≤ 0.
    Product of nonneg × nonneg × nonpos ≤ 0. -/
theorem k5_cert_nonpos : ∀ t, t ∈ Set.Icc (-1 : ℝ) (1/2) → k5_cert t ≤ 0 := by
  intro t ⟨_, ht_ub⟩
  unfold k5_cert
  have h1 : 0 ≤ (t + 5 / 7) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (t + 1 / 7) ^ 2 := sq_nonneg _
  have h3 : t - 1 / 2 ≤ 0 := by linarith
  have h12 : 0 ≤ (t + 5 / 7) ^ 2 * (t + 1 / 7) ^ 2 := mul_nonneg h1 h2
  exact mul_nonpos_of_nonneg_of_nonpos h12 h3

/-- f(1) = c₀ · 48. -/
theorem k5_bound_value : k5_cert 1 = k5_coeff 0 * 48 := by
  simp [k5_cert, k5_coeff]; ring

/-! ## Main upper bound theorem -/

/-- The kissing number in dimension 5 is at most 48.
    Uses the Delsarte LP bound with the certificate f(t) = (t+5/7)²(t+1/7)²(t-1/2).
    PSD for k=1,2,3 proved via feature maps; k=4,5 sorry'd. -/
theorem K5_le_48 : K 5 ≤ 48 := by
  apply sSup_le
  intro x hx
  obtain ⟨N, hN, rfl⟩ := hx
  obtain ⟨X, hX⟩ := hN
  obtain ⟨u, hunit, hinner⟩ := kissing_to_unit_sphere_5 hX
  have h_le : N ≤ 48 := delsarte_bound_5
    k5_cert k5_coeff 48 k5_expansion k5_coeff_pos k5_coeff_zero_pos
    k5_cert_nonpos k5_bound_value N u hunit hinner
    (fun k hk => P5_sum_nonneg u hunit k hk)
  exact WithTop.coe_le_coe.mpr h_le

/-- The lower bound K(5) ≥ 40 from the D5 root system. -/
private theorem forty_le_K5' : (40 : WithTop ℕ) ≤ K 5 :=
  le_K_of_exists exists_kissing_40

/-- Combined bounds: 40 ≤ K(5) ≤ 48. -/
theorem K5_bounds : (40 : WithTop ℕ) ≤ K 5 ∧ K 5 ≤ 48 :=
  ⟨forty_le_K5', K5_le_48⟩

end
