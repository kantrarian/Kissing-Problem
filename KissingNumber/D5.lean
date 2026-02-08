import KissingNumber.Defs
import KissingNumber.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

open scoped BigOperators RealInnerProductSpace
open Real WithLp

set_option linter.unusedSimpArgs false

abbrev Pair5 := {p : Fin 5 × Fin 5 // p.1 < p.2}
abbrev D5Sign2 := Bool × Bool
abbrev D5Index := Pair5 × D5Sign2

noncomputable section

def d5sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma d5sgn_true : d5sgn true = 1 := rfl
@[simp] lemma d5sgn_false : d5sgn false = -1 := rfl
lemma d5sgn_abs (b : Bool) : |d5sgn b| = 1 := by cases b <;> simp [d5sgn]
lemma d5sgn_mul_self (b : Bool) : d5sgn b * d5sgn b = 1 := by cases b <;> simp [d5sgn]
lemma d5sgn_sq (b : Bool) : d5sgn b ^ 2 = 1 := by cases b <;> simp [d5sgn]

abbrev d5iCoord (idx : D5Index) : Fin 5 := idx.1.1.1
abbrev d5jCoord (idx : D5Index) : Fin 5 := idx.1.1.2

lemma d5_i_ne_j (idx : D5Index) : d5iCoord idx ≠ d5jCoord idx := ne_of_lt idx.1.2

def d5Vec (idx : D5Index) : EuclideanSpace ℝ (Fin 5) :=
  toLp 2 (fun k =>
    if k = d5iCoord idx then d5sgn idx.2.1 * Real.sqrt 2
    else if k = d5jCoord idx then d5sgn idx.2.2 * Real.sqrt 2
    else 0)

lemma d5Vec_apply_i (idx : D5Index) : d5Vec idx (d5iCoord idx) = d5sgn idx.2.1 * Real.sqrt 2 := by
  simp only [d5Vec, PiLp.toLp_apply, ↓reduceIte]

lemma d5Vec_apply_j (idx : D5Index) : d5Vec idx (d5jCoord idx) = d5sgn idx.2.2 * Real.sqrt 2 := by
  have h : d5jCoord idx ≠ d5iCoord idx := (d5_i_ne_j idx).symm
  simp only [d5Vec, PiLp.toLp_apply, h, ↓reduceIte]

lemma d5Vec_apply_other {idx : D5Index} {k : Fin 5}
    (hki : k ≠ d5iCoord idx) (hkj : k ≠ d5jCoord idx) : d5Vec idx k = 0 := by
  simp only [d5Vec, PiLp.toLp_apply, hki, hkj, ↓reduceIte]

lemma norm_d5Vec (idx : D5Index) : ‖d5Vec idx‖ = 2 := by
  have h : ⟪d5Vec idx, d5Vec idx⟫ = (4 : ℝ) := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_add_of_pair (d5iCoord idx) (d5jCoord idx) (d5_i_ne_j idx)]
    · simp only [d5Vec_apply_i, d5Vec_apply_j, RCLike.inner_apply, conj_trivial]
      have h1 := d5sgn_mul_self idx.2.1
      have h2 := d5sgn_mul_self idx.2.2
      have hsq := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith
    · intro x hxi hxj
      simp only [d5Vec_apply_other hxi hxj, RCLike.inner_apply, conj_trivial, mul_zero]
  rw [norm_eq_sqrt_real_inner, h]
  rw [show (4:ℝ) = 2 ^ 2 from by norm_num]
  exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)

/-! Helper lemmas for inner product bound -/

private lemma d5_single_bound (s1 s2 : Bool) :
    (d5sgn s1 * Real.sqrt 2) * (d5sgn s2 * Real.sqrt 2) ≤ 2 := by
  have h : (d5sgn s1 * Real.sqrt 2) * (d5sgn s2 * Real.sqrt 2) =
           d5sgn s1 * d5sgn s2 * (Real.sqrt 2 * Real.sqrt 2) := by ring
  rw [h, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have : d5sgn s1 * d5sgn s2 ≤ 1 := by cases s1 <;> cases s2 <;> simp [d5sgn]
  nlinarith

private lemma d5_pair_bound (s1a s2a s1b s2b : Bool) (hne : (s1a, s2a) ≠ (s1b, s2b)) :
    (d5sgn s1b * Real.sqrt 2) * (d5sgn s1a * Real.sqrt 2) +
    (d5sgn s2b * Real.sqrt 2) * (d5sgn s2a * Real.sqrt 2) ≤ 2 := by
  have h1 : (d5sgn s1b * Real.sqrt 2) * (d5sgn s1a * Real.sqrt 2) =
             d5sgn s1b * d5sgn s1a * (Real.sqrt 2 * Real.sqrt 2) := by ring
  have h2 : (d5sgn s2b * Real.sqrt 2) * (d5sgn s2a * Real.sqrt 2) =
             d5sgn s2b * d5sgn s2a * (Real.sqrt 2 * Real.sqrt 2) := by ring
  rw [h1, h2, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hne' : s1a ≠ s1b ∨ s2a ≠ s2b := by
    by_contra hc; push_neg at hc; exact hne (Prod.ext hc.1 hc.2)
  rcases hne' with h | h
  · have : d5sgn s1b * d5sgn s1a = -1 := by cases s1a <;> cases s1b <;> simp [d5sgn] at h ⊢
    have : d5sgn s2b * d5sgn s2a ≤ 1 := by cases s2a <;> cases s2b <;> simp [d5sgn]
    nlinarith
  · have : d5sgn s2b * d5sgn s2a = -1 := by cases s2a <;> cases s2b <;> simp [d5sgn] at h ⊢
    have : d5sgn s1b * d5sgn s1a ≤ 1 := by cases s1a <;> cases s1b <;> simp [d5sgn]
    nlinarith

lemma inner_d5Vec_le_two (a b : D5Index) (hab : a ≠ b) :
    ⟪d5Vec a, d5Vec b⟫ ≤ (2 : ℝ) := by
  rw [PiLp.inner_apply]
  let ia := d5iCoord a; let ja := d5jCoord a
  let ib := d5iCoord b; let jb := d5jCoord b
  rw [Finset.sum_eq_add_of_pair ia ja (d5_i_ne_j a)]
  swap
  · intro k hki hkj
    simp only [RCLike.inner_apply, conj_trivial, d5Vec_apply_other hki hkj, mul_zero]
  rw [d5Vec_apply_i, d5Vec_apply_j]
  simp only [RCLike.inner_apply, conj_trivial]
  -- Goal: d5Vec b ia * (d5sgn a.2.1 * √2) + d5Vec b ja * (d5sgn a.2.2 * √2) ≤ 2
  by_cases hia_ib : ia = ib
  · -- ia = ib
    by_cases hja_jb : ja = jb
    · -- Same pair: signs must differ
      have h_pair : a.1 = b.1 := Subtype.ext (Prod.ext hia_ib hja_jb)
      have h_signs : a.2 ≠ b.2 := fun h' => hab (Prod.ext h_pair h')
      rw [hia_ib, d5Vec_apply_i, hja_jb, d5Vec_apply_j]
      exact d5_pair_bound a.2.1 a.2.2 b.2.1 b.2.2 h_signs
    · -- ia=ib, ja≠jb
      by_cases hja_ib : ja = ib
      · exact (d5_i_ne_j a (hia_ib.trans hja_ib.symm)).elim
      · have hja_zero : d5Vec b ja = 0 := d5Vec_apply_other hja_ib hja_jb
        rw [hia_ib, d5Vec_apply_i, hja_zero, zero_mul, add_zero]
        exact d5_single_bound b.2.1 a.2.1
  · -- ia ≠ ib
    by_cases hia_jb : ia = jb
    · -- ia = jb
      by_cases hja_ib : ja = ib
      · -- Cross match: contradicts ordering
        have h1 : (ia : ℕ) < (ja : ℕ) := a.1.2
        have h2 : (ib : ℕ) < (jb : ℕ) := b.1.2
        have : (jb : ℕ) < (ib : ℕ) := by rw [← hia_jb, ← hja_ib]; exact h1
        omega
      · by_cases hja_jb : ja = jb
        · exact (d5_i_ne_j a (hia_jb.trans hja_jb.symm)).elim
        · have hja_zero : d5Vec b ja = 0 := d5Vec_apply_other hja_ib hja_jb
          rw [hia_jb, d5Vec_apply_j, hja_zero, zero_mul, add_zero]
          exact d5_single_bound b.2.2 a.2.1
    · -- ia ≠ ib, ia ≠ jb → d5Vec b ia = 0
      have hia_zero : d5Vec b ia = 0 := d5Vec_apply_other hia_ib hia_jb
      by_cases hja_ib : ja = ib
      · rw [hia_zero, zero_mul, zero_add, hja_ib, d5Vec_apply_i]
        exact d5_single_bound b.2.1 a.2.2
      · by_cases hja_jb : ja = jb
        · rw [hia_zero, zero_mul, zero_add, hja_jb, d5Vec_apply_j]
          exact d5_single_bound b.2.2 a.2.2
        · have hja_zero : d5Vec b ja = 0 := d5Vec_apply_other hja_ib hja_jb
          rw [hia_zero, hja_zero, zero_mul, zero_mul]
          norm_num

theorem card_pair5 : Fintype.card Pair5 = 10 := by native_decide

theorem card_d5_index : Fintype.card D5Index = 40 := by native_decide

theorem exists_kissing_40 : ∃ X : Fin 40 → EuclideanSpace ℝ (Fin 5),
    IsKissingConfiguration 5 40 X := by
  let e := (Fintype.equivFinOfCardEq card_d5_index : D5Index ≃ Fin 40)
  let X := fun i => d5Vec (e.symm i)
  refine ⟨X, ?_, ?_⟩
  · intro i; exact norm_d5Vec (e.symm i)
  · intro i j hij
    have h_neq : e.symm i ≠ e.symm j := e.symm.injective.ne hij
    exact dist_ge_two_of_norm_eq_two_and_inner_le_two _ _
      (norm_d5Vec _) (norm_d5Vec _) (inner_d5Vec_le_two _ _ h_neq)

end
