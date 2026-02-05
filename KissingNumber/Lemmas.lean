import KissingNumber.Defs
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped BigOperators RealInnerProductSpace
open Real

/-- Sum over Finset.univ equals sum over two distinct elements plus sum over the rest. -/
lemma Finset.sum_eq_add_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (a b : ι) (hab : a ≠ b) (f : ι → M)
    (hrest : ∀ x, x ≠ a → x ≠ b → f x = 0) :
    ∑ x : ι, f x = f a + f b := by
  have h1 : ∑ x : ι, f x = ∑ x ∈ Finset.univ, f x := rfl
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x = a ∨ x = b)]
  have hfilter : Finset.univ.filter (fun x => x = a ∨ x = b) = {a, b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  rw [hfilter, Finset.sum_pair hab]
  have hrest_sum : ∑ x ∈ Finset.univ.filter (fun x => ¬(x = a ∨ x = b)), f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hx
    exact hrest x hx.1 hx.2
  rw [hrest_sum, add_zero]

/--
Bridge Lemma: If points have norm 2, sufficient to check inner product ≤ 2
to guarantee distance ≥ 2.
-/
lemma dist_ge_two_of_norm_eq_two_and_inner_le_two {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hnu : ‖u‖ = 2) (hnv : ‖v‖ = 2)
    (hinner : @Inner.inner ℝ _ _ u v ≤ (2:ℝ)) : ‖u - v‖ ≥ 2 := by
  have h_eq : ‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * @Inner.inner ℝ _ _ u v := by
    rw [norm_sub_sq_real]
    ring
  rw [hnu, hnv] at h_eq
  have h_bound : 4 ≤ ‖u - v‖^2 := by
    rw [h_eq]
    linarith
  have h_sqrt : Real.sqrt 4 ≤ Real.sqrt (‖u - v‖^2) := Real.sqrt_le_sqrt h_bound
  rw [Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  norm_num at h_sqrt
  exact h_sqrt

/--
Universal configuration validity lemma.
-/
lemma kissing_config_of_inner_le_two {d N : ℕ} (X : Fin N → EuclideanSpace ℝ (Fin d))
    (hnorm : ∀ i, ‖X i‖ = 2)
    (hinner : ∀ i j, i ≠ j → @Inner.inner ℝ _ _ (X i) (X j) ≤ (2:ℝ)) :
    IsKissingConfiguration d N X := by
  constructor
  · exact hnorm
  · intro i j hij
    apply dist_ge_two_of_norm_eq_two_and_inner_le_two
    · exact hnorm i
    · exact hnorm j
    · exact hinner i j hij
