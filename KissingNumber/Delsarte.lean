import KissingNumber.Defs
import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Delsarte Linear Programming Bound for Dimension 8

This file establishes the Delsarte LP bound framework:
1. A bridge lemma converting kissing configurations (norm 2, distance ≥ 2)
   to unit sphere configurations (norm 1, inner product ≤ 1/2).
2. The Delsarte bound theorem: given a certificate polynomial with PSD hypothesis,
   any such configuration has at most 240 points.

The PSD condition (positive semidefiniteness of Gegenbauer sums over the configuration)
is left as a hypothesis, not an axiom.
-/

open scoped BigOperators RealInnerProductSpace
open Real

noncomputable section

/-! ## Bridge Lemma: Kissing Configuration → Unit Sphere -/

/-- From a kissing configuration (norm 2, dist ≥ 2), we extract unit vectors
    with inner products ≤ 1/2 by scaling by 1/2. -/
theorem kissing_to_unit_sphere {N : ℕ} {X : Fin N → EuclideanSpace ℝ (Fin 8)}
    (hX : IsKissingConfiguration 8 N X) :
    ∃ u : Fin N → EuclideanSpace ℝ (Fin 8),
      (∀ i, ‖u i‖ = 1) ∧
      (∀ i j, i ≠ j → @inner ℝ _ _ (u i) (u j) ≤ (1 : ℝ) / 2) := by
  obtain ⟨hnorm, hdist⟩ := hX
  refine ⟨fun i => (2⁻¹ : ℝ) • X i, ?_, ?_⟩
  · intro i
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹), hnorm i]
    norm_num
  · intro i j hij
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    have h_dist := hdist i j hij
    have h_norm_sq : ‖X i - X j‖ ^ 2 = ‖X i‖ ^ 2 + ‖X j‖ ^ 2 - 2 * @inner ℝ _ _ (X i) (X j) := by
      rw [norm_sub_sq_real]; ring
    rw [hnorm i, hnorm j] at h_norm_sq
    have h_sq_ge : ‖X i - X j‖ ^ 2 ≥ 4 := by nlinarith [norm_nonneg (X i - X j)]
    have h_inner_le : @inner ℝ _ _ (X i) (X j) ≤ 2 := by linarith
    nlinarith

/-! ## Inner product bounds for unit vectors -/

/-- For unit vectors, inner product is at least -1 (from Cauchy-Schwarz). -/
lemma neg_one_le_inner_of_unit {u v : EuclideanSpace ℝ (Fin 8)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    -1 ≤ @inner ℝ _ _ u v := by
  have h := abs_real_inner_le_norm u v
  rw [hu, hv, mul_one] at h
  exact neg_le_of_abs_le h

/-- The self inner product of a unit vector is 1. -/
lemma inner_self_eq_one_of_unit {u : EuclideanSpace ℝ (Fin 8)}
    (hu : ‖u‖ = 1) :
    @inner ℝ _ _ u u = 1 := by
  rw [real_inner_self_eq_norm_sq, hu, one_pow]

/-! ## Delsarte Bound Theorem -/

/--
**Delsarte LP bound for dimension 8.**

Given a certificate polynomial `f` with Gegenbauer expansion coefficients `c`,
satisfying the standard LP conditions plus PSD hypotheses on the configuration,
any unit-sphere configuration with pairwise inner products ≤ 1/2 has ≤ 240 points.
-/
theorem delsarte_bound_8
    (f : ℝ → ℝ) (c : Fin 7 → ℝ)
    (hexp : ∀ t, f t = ∑ k : Fin 7, c k * P8 k t)
    (hpos : ∀ k : Fin 7, k ≠ 0 → 0 ≤ c k)
    (hc0 : 0 < c 0)
    (hneg : ∀ t, t ∈ Set.Icc (-1 : ℝ) (1 / 2) → f t ≤ 0)
    (hf1 : f 1 = c 0 * 240)
    (N : ℕ) (u : Fin N → EuclideanSpace ℝ (Fin 8))
    (hunit : ∀ i, ‖u i‖ = 1)
    (hinner : ∀ i j, i ≠ j → @inner ℝ _ _ (u i) (u j) ≤ (1 : ℝ) / 2)
    (hpsd : ∀ k : Fin 7, k ≠ 0 →
        0 ≤ ∑ i : Fin N, ∑ j : Fin N, P8 k (@inner ℝ _ _ (u i) (u j))) :
    N ≤ 240 := by
  -- Handle N = 0 trivially
  by_cases hN : N = 0
  · omega
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
  -- Key quantity: S_k := ∑ᵢ ∑ⱼ P8 k ⟪uᵢ, uⱼ⟫
  set S := fun k : Fin 7 => ∑ i : Fin N, ∑ j : Fin N, P8 k (@inner ℝ _ _ (u i) (u j)) with hS_def

  -- Step 1: S 0 = N² (since P8 0 = 1)
  have hS0 : S 0 = (N : ℝ) ^ 2 := by
    simp only [hS_def, P8_0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring

  -- Step 2: ∑ₖ cₖ · Sₖ = ∑ᵢ ∑ⱼ f(⟪uᵢ,uⱼ⟫)
  have h_total : ∑ k : Fin 7, c k * S k =
      ∑ i : Fin N, ∑ j : Fin N, f (@inner ℝ _ _ (u i) (u j)) := by
    simp_rw [hS_def, hexp, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext i
    rw [Finset.sum_comm]

  -- Step 3: Lower bound: ∑ₖ cₖ · Sₖ ≥ c₀ · N²
  have h_nonneg_terms : ∀ k : Fin 7, k ≠ 0 → 0 ≤ c k * S k :=
    fun k hk => mul_nonneg (hpos k hk) (hpsd k hk)
  have h_lower : c 0 * (N : ℝ) ^ 2 ≤ ∑ k : Fin 7, c k * S k := by
    rw [← hS0]
    have h_split := Finset.add_sum_erase Finset.univ (fun k => c k * S k) (Finset.mem_univ (0 : Fin 7))
    rw [← h_split]
    linarith [Finset.sum_nonneg (fun k (hk : k ∈ Finset.univ.erase (0 : Fin 7)) =>
      h_nonneg_terms k (Finset.ne_of_mem_erase hk))]

  -- Step 4: Upper bound: ∑ᵢ ∑ⱼ f(⟪uᵢ,uⱼ⟫) ≤ N · f(1)
  have h_diag : ∀ i : Fin N, f (@inner ℝ _ _ (u i) (u i)) = f 1 := by
    intro i; congr 1; exact inner_self_eq_one_of_unit (hunit i)
  have h_upper : ∑ i : Fin N, ∑ j : Fin N, f (@inner ℝ _ _ (u i) (u j)) ≤
      (N : ℝ) * f 1 := by
    calc ∑ i : Fin N, ∑ j : Fin N, f (@inner ℝ _ _ (u i) (u j))
        ≤ ∑ _i : Fin N, f 1 := by
          apply Finset.sum_le_sum
          intro i _
          calc ∑ j : Fin N, f (@inner ℝ _ _ (u i) (u j))
              = f (@inner ℝ _ _ (u i) (u i)) +
                ∑ j ∈ Finset.univ.erase i, f (@inner ℝ _ _ (u i) (u j)) :=
                (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
            _ ≤ f 1 + 0 := by
                gcongr
                · exact le_of_eq (h_diag i)
                · apply Finset.sum_nonpos
                  intro j hj
                  apply hneg
                  exact ⟨neg_one_le_inner_of_unit (hunit i) (hunit j),
                         hinner i j (Finset.ne_of_mem_erase hj).symm⟩
            _ = f 1 := add_zero _
      _ = (N : ℝ) * f 1 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  -- Step 5: Combine: c₀ · N² ≤ N · f(1) = N · c₀ · 240
  have h_combined : c 0 * (N : ℝ) ^ 2 ≤ (N : ℝ) * (c 0 * 240) := by
    calc c 0 * (N : ℝ) ^ 2 ≤ ∑ k : Fin 7, c k * S k := h_lower
      _ = ∑ i : Fin N, ∑ j : Fin N, f (@inner ℝ _ _ (u i) (u j)) := h_total
      _ ≤ (N : ℝ) * f 1 := h_upper
      _ = (N : ℝ) * (c 0 * 240) := by rw [hf1]

  -- Step 6: Divide by c₀ · N (both positive): N ≤ 240
  have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  have hcN : 0 < c 0 * (N : ℝ) := mul_pos hc0 hN_pos_real
  have h_le_real : (N : ℝ) ≤ 240 := by nlinarith
  exact_mod_cast h_le_real

end
