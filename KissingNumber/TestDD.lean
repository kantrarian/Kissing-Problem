import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Finset

noncomputable section

private abbrev T6 := Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8

private def D6t (_x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if a=b then 1 else 0) * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + (if a=c then 1 else 0) * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  + (if a=d then 1 else 0) * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + (if a=e then 1 else 0) * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + (if a=f then 1 else 0) * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))

private lemma sum_ite_prop_zero' {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

-- Test: delta collapse for DD with high heartbeats
set_option maxHeartbeats 400000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : T6, D6t x p * D6t y p = 14400 := by
  simp only [D6t]
  simp_rw [Fintype.sum_prod_type]
  -- Distribution: (sum of 15 terms) * (sum of 15 terms) = 225 terms
  simp (config := { maxSteps := 100000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  -- Handle ite multiplication
  simp (config := { maxSteps := 100000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  -- Delta collapse
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- After collapse, should be sums of 1's = multiples of 8
  -- Each sum ∑ 1 over Fin 8 = 8, and ∑∑ 1 = 64, ∑∑∑ 1 = 512
  norm_num

end
