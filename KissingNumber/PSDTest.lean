import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

def phi2 (x : EuclideanSpace ℝ (Fin 8)) (p : Fin 8 × Fin 8) : ℝ :=
  x p.1 * x p.2 - if p.1 = p.2 then (1 : ℝ) / 8 else 0

lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]
  congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

lemma phi2_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : Fin 8 × Fin 8, phi2 x p * phi2 y p =
    (7 : ℝ) / 8 * P8 2 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : Fin 8 × Fin 8, phi2 x p * phi2 y p =
      (@inner ℝ _ _ x y) ^ 2 - 1 / 8 by
    rw [h, P8_2]; ring
  simp only [phi2]
  rw [Fintype.sum_prod_type]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hA : ∑ a : Fin 8, ∑ b : Fin 8,
      x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (@inner ℝ _ _ x y) ^ 2 := by
    rw [inner_ofLp, sq, Finset.sum_mul]
    congr 1; ext a; rw [Finset.mul_sum]
    congr 1; ext b; ring
  have hB : ∑ a : Fin 8, x.ofLp a * x.ofLp a * (1 / 8) = 1 / 8 := by
    rw [← Finset.sum_mul, ofLp_norm_sq x hx]; ring
  have hC : ∑ a : Fin 8, 1 / 8 * (y.ofLp a * y.ofLp a) = 1 / 8 := by
    rw [← Finset.mul_sum, ofLp_norm_sq y hy]; ring
  have hD : ∑ _a : Fin 8, (1 : ℝ) / 8 * (1 / 8) = 1 / 8 := by
    simp [Finset.sum_const, Fintype.card_fin]
  linarith

end
