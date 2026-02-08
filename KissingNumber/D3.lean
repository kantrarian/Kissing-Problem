import KissingNumber.Defs
import KissingNumber.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real WithLp

set_option linter.unusedSimpArgs false

abbrev Pair3 := {p : Fin 3 × Fin 3 // p.1 < p.2}
abbrev D3Index := Pair3 × (Bool × Bool)

noncomputable section

def d3sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma d3sgn_true : d3sgn true = 1 := rfl
@[simp] lemma d3sgn_false : d3sgn false = -1 := rfl
lemma d3sgn_abs (b : Bool) : |d3sgn b| = 1 := by cases b <;> simp [d3sgn]
lemma d3sgn_mul_self (b : Bool) : d3sgn b * d3sgn b = 1 := by cases b <;> simp [d3sgn]
lemma d3sgn_sq (b : Bool) : d3sgn b ^ 2 = 1 := by cases b <;> simp [d3sgn]

abbrev d3iCoord (idx : D3Index) : Fin 3 := idx.1.1.1
abbrev d3jCoord (idx : D3Index) : Fin 3 := idx.1.1.2

lemma d3_i_ne_j (idx : D3Index) : d3iCoord idx ≠ d3jCoord idx := ne_of_lt idx.1.2

def d3Vec (idx : D3Index) : EuclideanSpace ℝ (Fin 3) :=
  toLp 2 (fun k =>
    if k = d3iCoord idx then d3sgn idx.2.1 * Real.sqrt 2
    else if k = d3jCoord idx then d3sgn idx.2.2 * Real.sqrt 2
    else 0)

lemma d3Vec_apply_i (idx : D3Index) : d3Vec idx (d3iCoord idx) = d3sgn idx.2.1 * Real.sqrt 2 := by
  simp only [d3Vec, PiLp.toLp_apply, ↓reduceIte]

lemma d3Vec_apply_j (idx : D3Index) : d3Vec idx (d3jCoord idx) = d3sgn idx.2.2 * Real.sqrt 2 := by
  have h : d3jCoord idx ≠ d3iCoord idx := (d3_i_ne_j idx).symm
  simp only [d3Vec, PiLp.toLp_apply, h, ↓reduceIte]

lemma d3Vec_apply_other {idx : D3Index} {k : Fin 3}
    (hki : k ≠ d3iCoord idx) (hkj : k ≠ d3jCoord idx) : d3Vec idx k = 0 := by
  simp only [d3Vec, PiLp.toLp_apply, hki, hkj, ↓reduceIte]

lemma norm_d3Vec (idx : D3Index) : ‖d3Vec idx‖ = 2 := by
  have h : ⟪d3Vec idx, d3Vec idx⟫ = (4 : ℝ) := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_add_of_pair (d3iCoord idx) (d3jCoord idx) (d3_i_ne_j idx)]
    · simp only [d3Vec_apply_i, d3Vec_apply_j, RCLike.inner_apply, conj_trivial]
      have h1 := d3sgn_mul_self idx.2.1
      have h2 := d3sgn_mul_self idx.2.2
      have hsq := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith
    · intro x hxi hxj
      simp only [d3Vec_apply_other hxi hxj, RCLike.inner_apply, conj_trivial, mul_zero]
  rw [norm_eq_sqrt_real_inner, h]
  rw [show (4:ℝ) = 2 ^ 2 from by norm_num]
  exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)

/-! Helper lemmas for inner product bound -/

private lemma d3_single_bound (s1 s2 : Bool) :
    (d3sgn s1 * Real.sqrt 2) * (d3sgn s2 * Real.sqrt 2) ≤ 2 := by
  have h : (d3sgn s1 * Real.sqrt 2) * (d3sgn s2 * Real.sqrt 2) =
           d3sgn s1 * d3sgn s2 * (Real.sqrt 2 * Real.sqrt 2) := by ring
  rw [h, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have : d3sgn s1 * d3sgn s2 ≤ 1 := by cases s1 <;> cases s2 <;> simp [d3sgn]
  nlinarith

private lemma d3_pair_bound (s1a s2a s1b s2b : Bool) (hne : (s1a, s2a) ≠ (s1b, s2b)) :
    (d3sgn s1b * Real.sqrt 2) * (d3sgn s1a * Real.sqrt 2) +
    (d3sgn s2b * Real.sqrt 2) * (d3sgn s2a * Real.sqrt 2) ≤ 2 := by
  have h1 : (d3sgn s1b * Real.sqrt 2) * (d3sgn s1a * Real.sqrt 2) =
             d3sgn s1b * d3sgn s1a * (Real.sqrt 2 * Real.sqrt 2) := by ring
  have h2 : (d3sgn s2b * Real.sqrt 2) * (d3sgn s2a * Real.sqrt 2) =
             d3sgn s2b * d3sgn s2a * (Real.sqrt 2 * Real.sqrt 2) := by ring
  rw [h1, h2, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hne' : s1a ≠ s1b ∨ s2a ≠ s2b := by
    by_contra hc; push_neg at hc; exact hne (Prod.ext hc.1 hc.2)
  rcases hne' with h | h
  · have : d3sgn s1b * d3sgn s1a = -1 := by cases s1a <;> cases s1b <;> simp [d3sgn] at h ⊢
    have : d3sgn s2b * d3sgn s2a ≤ 1 := by cases s2a <;> cases s2b <;> simp [d3sgn]
    nlinarith
  · have : d3sgn s2b * d3sgn s2a = -1 := by cases s2a <;> cases s2b <;> simp [d3sgn] at h ⊢
    have : d3sgn s1b * d3sgn s1a ≤ 1 := by cases s1a <;> cases s1b <;> simp [d3sgn]
    nlinarith

lemma inner_d3Vec_le_two (a b : D3Index) (hab : a ≠ b) :
    ⟪d3Vec a, d3Vec b⟫ ≤ (2 : ℝ) := by
  rw [PiLp.inner_apply]
  let ia := d3iCoord a; let ja := d3jCoord a
  let ib := d3iCoord b; let jb := d3jCoord b
  rw [Finset.sum_eq_add_of_pair ia ja (d3_i_ne_j a)]
  swap
  · intro k hki hkj
    simp only [RCLike.inner_apply, conj_trivial, d3Vec_apply_other hki hkj, mul_zero]
  rw [d3Vec_apply_i, d3Vec_apply_j]
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hia_ib : ia = ib
  · by_cases hja_jb : ja = jb
    · -- Same pair: signs must differ
      have h_pair : a.1 = b.1 := Subtype.ext (Prod.ext hia_ib hja_jb)
      have h_signs : a.2 ≠ b.2 := fun h' => hab (Prod.ext h_pair h')
      rw [hia_ib, d3Vec_apply_i, hja_jb, d3Vec_apply_j]
      exact d3_pair_bound a.2.1 a.2.2 b.2.1 b.2.2 h_signs
    · by_cases hja_ib : ja = ib
      · exact (d3_i_ne_j a (hia_ib.trans hja_ib.symm)).elim
      · have hja_zero : d3Vec b ja = 0 := d3Vec_apply_other hja_ib hja_jb
        rw [hia_ib, d3Vec_apply_i, hja_zero, zero_mul, add_zero]
        exact d3_single_bound b.2.1 a.2.1
  · by_cases hia_jb : ia = jb
    · by_cases hja_ib : ja = ib
      · -- Cross match: contradicts ordering
        have h1 : (ia : ℕ) < (ja : ℕ) := a.1.2
        have h2 : (ib : ℕ) < (jb : ℕ) := b.1.2
        have : (jb : ℕ) < (ib : ℕ) := by rw [← hia_jb, ← hja_ib]; exact h1
        omega
      · by_cases hja_jb : ja = jb
        · exact (d3_i_ne_j a (hia_jb.trans hja_jb.symm)).elim
        · have hja_zero : d3Vec b ja = 0 := d3Vec_apply_other hja_ib hja_jb
          rw [hia_jb, d3Vec_apply_j, hja_zero, zero_mul, add_zero]
          exact d3_single_bound b.2.2 a.2.1
    · have hia_zero : d3Vec b ia = 0 := d3Vec_apply_other hia_ib hia_jb
      by_cases hja_ib : ja = ib
      · rw [hia_zero, zero_mul, zero_add, hja_ib, d3Vec_apply_i]
        exact d3_single_bound b.2.1 a.2.2
      · by_cases hja_jb : ja = jb
        · rw [hia_zero, zero_mul, zero_add, hja_jb, d3Vec_apply_j]
          exact d3_single_bound b.2.2 a.2.2
        · have hja_zero : d3Vec b ja = 0 := d3Vec_apply_other hja_ib hja_jb
          rw [hia_zero, hja_zero, zero_mul, zero_mul]
          norm_num

theorem card_pair3 : Fintype.card Pair3 = 3 := by native_decide

theorem card_d3_index : Fintype.card D3Index = 12 := by native_decide

theorem exists_kissing_12 : ∃ X : Fin 12 → EuclideanSpace ℝ (Fin 3),
    IsKissingConfiguration 3 12 X := by
  let e := (Fintype.equivFinOfCardEq card_d3_index : D3Index ≃ Fin 12)
  let X := fun i => d3Vec (e.symm i)
  refine ⟨X, ?_, ?_⟩
  · intro i; exact norm_d3Vec (e.symm i)
  · intro i j hij
    have h_neq : e.symm i ≠ e.symm j := e.symm.injective.ne hij
    exact dist_ge_two_of_norm_eq_two_and_inner_le_two _ _
      (norm_d3Vec _) (norm_d3Vec _) (inner_d3Vec_le_two _ _ h_neq)

end
