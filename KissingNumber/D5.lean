import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

open scoped BigOperators RealInnerProductSpace
open Real

abbrev R5 : Type := EuclideanSpace ℝ (Fin 5)

-- A D5 index is a pair of distinct coordinates (p.1 < p.2) and two signs
abbrev Pair5 := {p : Fin 5 × Fin 5 // p.1 < p.2}
abbrev Sign2 := Bool × Bool
abbrev D5Index := Pair5 × Sign2

noncomputable def sgn (b : Bool) : ℝ := if b then (1:ℝ) else (-1)

-- Definition of the 40 vectors of the D5 root system (scaled to norm 2)
-- Each vector has exactly two non-zero coordinates with value ±√2.
noncomputable def d5Vec (idx : D5Index) : R5 :=
  let i := idx.1.1.1
  let j := idx.1.1.2
  let si := sgn idx.2.1
  let sj := sgn idx.2.2
  fun k =>
    if k = i then si * Real.sqrt 2
    else if k = j then sj * Real.sqrt 2
    else 0

-- Helper lemma: sgn squared is 1
lemma sgn_sq (b : Bool) : (sgn b)^2 = (1:ℝ) := by
  by_cases hb : b <;> simp [sgn, hb]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = (1:ℝ) := by
  by_cases hb : b <;> simp [sgn, hb]

-- Accessors for coordinates
noncomputable def iCoord (idx : D5Index) : Fin 5 := idx.1.1.1
noncomputable def jCoord (idx : D5Index) : Fin 5 := idx.1.1.2

lemma iCoord_ne_jCoord (idx : D5Index) : iCoord idx ≠ jCoord idx :=
  ne_of_lt idx.1.2

-- Helper lemmas for evaluating d5Vec
lemma d5Vec_apply_i (idx : D5Index) : d5Vec idx (iCoord idx) = sgn idx.2.1 * Real.sqrt 2 := by
  simp [d5Vec, iCoord, jCoord, iCoord_ne_jCoord]

lemma d5Vec_apply_j (idx : D5Index) : d5Vec idx (jCoord idx) = sgn idx.2.2 * Real.sqrt 2 := by
  let i := idx.1.1.1
  let j := idx.1.1.2
  have h : j ≠ i := (ne_of_lt idx.1.2).symm
  simp [d5Vec, iCoord, jCoord, h]

lemma d5Vec_apply_other {idx : D5Index} {k : Fin 5} (hk1 : k ≠ iCoord idx) (hk2 : k ≠ jCoord idx) :
    d5Vec idx k = 0 := by
  simp [d5Vec, iCoord, jCoord, hk1, hk2]

-- Lemma 1: All vectors have norm 2
lemma norm_d5Vec (idx : D5Index) : ‖d5Vec idx‖ = 2 := by
  have h : ⟪d5Vec idx, d5Vec idx⟫_ℝ = 4 := by
    unfold inner PiLp.inner
    rw [Finset.sum_eq_add_of_mem (Finset.mem_univ (iCoord idx)) (Finset.mem_univ (jCoord idx)) (iCoord_ne_jCoord idx)]
    · simp [d5Vec_apply_i, d5Vec_apply_j, sgn_sq]
      ring
    · intro x hxi hxj
      rw [d5Vec_apply_other hxi hxj]
      simp
  exact Real.norm_of_inner_self_eq_sq (by norm_num) h

-- Lemma 2: Inner product is at most 2 for distinct vectors
lemma inner_d5Vec_le_two (a b : D5Index) (hab : a ≠ b) :
    ⟪d5Vec a, d5Vec b⟫_ℝ ≤ 2 := by
  -- Reduce sum to support of a
  rw [inner_sum]
  rw [Finset.sum_eq_add_of_mem (Finset.mem_univ (iCoord a)) (Finset.mem_univ (jCoord a)) (iCoord_ne_jCoord a)]
  · -- Evaluate terms on support of a
    rw [d5Vec_apply_i, d5Vec_apply_j]
    let ia := iCoord a
    let ja := jCoord a
    let ib := iCoord b
    let jb := jCoord b
    by_cases h1 : ia = ib ∨ ia = jb
    case pos =>
       -- ia hits b
       by_cases h2 : ja = ib ∨ ja = jb
       case pos =>
         -- both hit b => pair is same => sign differs => -4 or 0
         have h_pair_eq : a.1 = b.1 := by
           cases h1 with h1l h1r <;> cases h2 with h2l h2r
           · ext; simp [ia, ib] at h1l; simp [ja, ib] at h2l; rw [←h1l] at h2l; exact (iCoord_ne_jCoord a h2l).elim
           · ext; simp [ia, ib] at h1l; simp [ja, jb] at h2r; simp [h1l, h2r]; have : a.1.1 = b.1.1 := h1l; have : a.1.2 = b.1.2 := h2r; simp [this]
           · linarith [a.1.2, b.1.2] -- ia=jb, ja=ib contradiction handled by linarith on indices
           · ext; simp [ia, jb] at h1r; simp [ja, jb] at h2r; rw [←h1r] at h2r; exact (iCoord_ne_jCoord a h2r).elim
         
         -- If we are here, a.1 = b.1.
         have h_signs_ne : a.2 ≠ b.2 := by
           intro h
           apply hab
           ext
           · exact h_pair_eq
           · exact h
         
         rw [if_pos h1, if_pos h2]
         have hia : ia = ib := by rw [h_pair_eq]
         have hja : ja = jb := by rw [h_pair_eq]
         rw [hia, d5Vec_apply_i, hja, d5Vec_apply_j]
         
         replace h_signs_ne : a.2.1 ≠ b.2.1 ∨ a.2.2 ≠ b.2.2 := by
           contrapose! h_signs_ne
           ext <;> simp [h_signs_ne]
         
         cases h_signs_ne with hs1 hs2
         · -- First sign differs
           rw [← sgn_mul_self b.2.1]
           have : sgn a.2.1 * sgn b.2.1 = -1 := by
             simp [sgn]; split_ifs at hs1 with hx hy <;> simp at hs1 <;> simp [hx, hy]
             exact hs1
             exact hs1.symm
           simp [this]
           apply add_le_add
           . norm_num
           . rw [← mul_assoc]
             nth_rewrite 2 [← one_mul (2:ℝ)]
             apply mul_le_mul_of_nonneg_right
             . simp [sgn]; split_ifs <;> norm_num
             . norm_num
           
         · -- Second sign differs
           have : sgn a.2.2 * sgn b.2.2 = -1 := by
             simp [sgn]; split_ifs at hs2 with hx hy <;> simp at hs2 <;> simp [hx, hy]
             exact hs2
             exact hs2.symm
           simp [this]
           apply add_le_add
           . rw [← mul_assoc]
             nth_rewrite 2 [← one_mul (2:ℝ)]
             apply mul_le_mul_of_nonneg_right
             . simp [sgn]; split_ifs <;> norm_num
             . norm_num
           . norm_num
 
       case neg =>
         -- ia hits b (h1), ja does not. One match => ±2.
         have : d5Vec b ja = 0 := by
            push_neg at h2
            apply d5Vec_apply_other h2.1 h2.2
         rw [this, mul_zero, add_zero]
         cases h1 with
         | inl hia =>
           rw [hia, d5Vec_apply_i]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
         | inr hia =>
           rw [hia, d5Vec_apply_j]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
 
    case neg =>
       -- ia does not hit b.
       have hia : d5Vec b ia = 0 := by
         push_neg at h1
         apply d5Vec_apply_other h1.1 h1.2
       rw [hia, mul_zero, zero_add]
       by_cases h2 : ja = ib ∨ ja = jb
       case pos =>
         -- ja hits b. One match => ±2.
         cases h2 with
         | inl hja =>
           rw [hja, d5Vec_apply_i]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
         | inr hja =>
           rw [hja, d5Vec_apply_j]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
       case neg =>
         -- Neither hits. Inner product 0.
         have hja : d5Vec b ja = 0 := by
            push_neg at h2
            apply d5Vec_apply_other h2.1 h2.2
         rw [hja, mul_zero]
         norm_num
 
  · intro x hxi hxj
    -- Outside support of a
    rw [d5Vec_apply_other hxi hxj, zero_mul]

-- Lemma 3: Pairwise distance is at least 2
lemma dist_d5Vec_ge_two (a b : D5Index) (hab : a ≠ b) :
    ‖d5Vec a - d5Vec b‖ ≥ 2 := by
  have h_sq : ‖d5Vec a - d5Vec b‖^2 = ‖d5Vec a‖^2 + ‖d5Vec b‖^2 - 2 * ⟪d5Vec a, d5Vec b⟫_ℝ :=
    norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_real_inner (d5Vec a) (d5Vec b)
  rw [norm_d5Vec a, norm_d5Vec b] at h_sq
  norm_num at h_sq
  have h_inner := inner_d5Vec_le_two a b hab
  have h_bound : 8 - 2 * ⟪d5Vec a, d5Vec b⟫_ℝ ≥ 4 := by linarith
  rw [h_sq] at h_bound
  rw [ge_iff_le]
  apply Real.le_sqrt_of_sq_le
  . norm_num [h_bound]

def IsKissingConfiguration (N : ℕ) (X : Fin N → R5) : Prop :=
  (∀ i, ‖X i‖ = 2) ∧ (∀ i j, i ≠ j → ‖X i - X j‖ ≥ 2)

theorem card_pair5 : Fintype.card Pair5 = 10 := by
  native_decide

theorem card_d5_index : Fintype.card D5Index = 40 := by
  simp only [D5Index, Sign2]
  rw [Fintype.card_prod, card_pair5, Fintype.card_prod, Fintype.card_bool]
  try norm_num

theorem exists_kissing_40 : ∃ X : Fin 40 → R5, IsKissingConfiguration 40 X := by
  -- Construct the equivalence
  let d5_equiv : D5Index ≃ Fin 40 :=
    Fintype.equivFinOfCardEq card_d5_index.symm
  let e := d5_equiv.symm
  
  -- Define X
  let X := fun (i : Fin 40) => d5Vec (e i)
  use X
  
  -- Prove IsKissingConfiguration
  constructor
  · intro i
    simp [X]
    apply norm_d5Vec
  · intro i j hij
    simp [X]
    have h_neq : e i ≠ e j := d5_equiv.symm.injective.ne hij
    apply dist_d5Vec_ge_two
    exact h_neq

open scoped BigOperators RealInnerProductSpace
open Real

abbrev R5 : Type := EuclideanSpace ℝ (Fin 5)

-- A D5 index is a pair of distinct coordinates (p.1 < p.2) and two signs
abbrev Pair5 := {p : Fin 5 × Fin 5 // p.1 < p.2}
abbrev Sign2 := Bool × Bool
abbrev D5Index := Pair5 × Sign2

noncomputable def sgn (b : Bool) : ℝ := if b then (1:ℝ) else (-1)

-- Definition of the 40 vectors of the D5 root system (scaled to norm 2)
-- Each vector has exactly two non-zero coordinates with value ±√2.
noncomputable def d5Vec (idx : D5Index) : R5 :=
  let i := idx.1.1.1
  let j := idx.1.1.2
  let si := sgn idx.2.1
  let sj := sgn idx.2.2
  fun k =>
    if k = i then si * Real.sqrt 2
    else if k = j then sj * Real.sqrt 2
    else 0

-- Helper lemma: sgn squared is 1
lemma sgn_sq (b : Bool) : (sgn b)^2 = (1:ℝ) := by
  by_cases hb : b <;> simp [sgn, hb]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = (1:ℝ) := by
  by_cases hb : b <;> simp [sgn, hb]

-- Accessors for coordinates
noncomputable def iCoord (idx : D5Index) : Fin 5 := idx.1.1.1
noncomputable def jCoord (idx : D5Index) : Fin 5 := idx.1.1.2

lemma iCoord_ne_jCoord (idx : D5Index) : iCoord idx ≠ jCoord idx :=
  ne_of_lt idx.1.2

-- Helper lemmas for evaluating d5Vec
lemma d5Vec_apply_i (idx : D5Index) : d5Vec idx (iCoord idx) = sgn idx.2.1 * Real.sqrt 2 := by
  simp [d5Vec, iCoord, jCoord, iCoord_ne_jCoord]

lemma d5Vec_apply_j (idx : D5Index) : d5Vec idx (jCoord idx) = sgn idx.2.2 * Real.sqrt 2 := by
  let i := idx.1.1.1
  let j := idx.1.1.2
  have h : j ≠ i := (ne_of_lt idx.1.2).symm
  simp [d5Vec, iCoord, jCoord, h]

lemma d5Vec_apply_other {idx : D5Index} {k : Fin 5} (hk1 : k ≠ iCoord idx) (hk2 : k ≠ jCoord idx) :
    d5Vec idx k = 0 := by
  simp [d5Vec, iCoord, jCoord, hk1, hk2]

-- Lemma 1: All vectors have norm 2
lemma norm_d5Vec (idx : D5Index) : ‖d5Vec idx‖ = 2 := by
  have h : inner (d5Vec idx) (d5Vec idx) = (4:ℝ) := by
    unfold inner PiLp.inner
    rw [Finset.sum_eq_add_of_mem (Finset.mem_univ (iCoord idx)) (Finset.mem_univ (jCoord idx)) (iCoord_ne_jCoord idx)]
    · simp [d5Vec_apply_i, d5Vec_apply_j, sgn_sq]
      ring
    · intro x hxi hxj
      rw [d5Vec_apply_other hxi hxj]
      simp
  exact Real.norm_of_inner_self_eq_sq (by norm_num) h

-- Lemma 2: Inner product is at most 2 for distinct vectors
lemma inner_d5Vec_le_two (a b : D5Index) (hab : a ≠ b) :
    ⟪d5Vec a, d5Vec b⟫_ℝ ≤ 2 := by
  -- Reduce sum to support of a
  rw [inner_sum]
  rw [Finset.sum_eq_add_of_mem (Finset.mem_univ (iCoord a)) (Finset.mem_univ (jCoord a)) (iCoord_ne_jCoord a)]
  · -- Evaluate terms on support of a
    rw [d5Vec_apply_i, d5Vec_apply_j]
    let ia := iCoord a
    let ja := jCoord a
    let ib := iCoord b
    let jb := jCoord b
    by_cases h1 : ia = ib ∨ ia = jb
    case pos =>
       -- ia hits b
       by_cases h2 : ja = ib ∨ ja = jb
       case pos =>
         -- both hit b => pair is same => sign differs => -4 or 0
         have h_pair_eq : a.1 = b.1 := by
           cases h1 with h1l h1r <;> cases h2 with h2l h2r
           · ext; simp [ia, ib] at h1l; simp [ja, ib] at h2l; rw [←h1l] at h2l; exact (iCoord_ne_jCoord a h2l).elim
           · ext; simp [ia, ib] at h1l; simp [ja, jb] at h2r; simp [h1l, h2r]; have : a.1.1 = b.1.1 := h1l; have : a.1.2 = b.1.2 := h2r; simp [this]
           · linarith [a.1.2, b.1.2] -- ia=jb, ja=ib contradiction handled by linarith on indices
           · ext; simp [ia, jb] at h1r; simp [ja, jb] at h2r; rw [←h1r] at h2r; exact (iCoord_ne_jCoord a h2r).elim
         
         -- If we are here, a.1 = b.1.
         have h_signs_ne : a.2 ≠ b.2 := by
           intro h
           apply hab
           ext
           · exact h_pair_eq
           · exact h
         
         rw [if_pos h1, if_pos h2]
         have hia : ia = ib := by rw [h_pair_eq]
         have hja : ja = jb := by rw [h_pair_eq]
         rw [hia, d5Vec_apply_i, hja, d5Vec_apply_j]
         
         replace h_signs_ne : a.2.1 ≠ b.2.1 ∨ a.2.2 ≠ b.2.2 := by
           contrapose! h_signs_ne
           ext <;> simp [h_signs_ne]
         
         cases h_signs_ne with hs1 hs2
         · -- First sign differs
           rw [← sgn_mul_self b.2.1]
           have : sgn a.2.1 * sgn b.2.1 = -1 := by
             simp [sgn]; split_ifs at hs1 with hx hy <;> simp at hs1 <;> simp [hx, hy]
             exact hs1
             exact hs1.symm
           simp [this]
           apply add_le_add
           . norm_num
           . rw [← mul_assoc]
             nth_rewrite 2 [← one_mul (2:ℝ)]
             apply mul_le_mul_of_nonneg_right
             . simp [sgn]; split_ifs <;> norm_num
             . norm_num
           
         · -- Second sign differs
           have : sgn a.2.2 * sgn b.2.2 = -1 := by
             simp [sgn]; split_ifs at hs2 with hx hy <;> simp at hs2 <;> simp [hx, hy]
             exact hs2
             exact hs2.symm
           simp [this]
           apply add_le_add
           . rw [← mul_assoc]
             nth_rewrite 2 [← one_mul (2:ℝ)]
             apply mul_le_mul_of_nonneg_right
             . simp [sgn]; split_ifs <;> norm_num
             . norm_num
           . norm_num

       case neg =>
         -- ia hits b (h1), ja does not. One match => ±2.
         have : d5Vec b ja = 0 := by
            push_neg at h2
            apply d5Vec_apply_other h2.1 h2.2
         rw [this, mul_zero, add_zero]
         cases h1 with
         | inl hia =>
           rw [hia, d5Vec_apply_i]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
         | inr hia =>
           rw [hia, d5Vec_apply_j]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num

    case neg =>
       -- ia does not hit b.
       have hia : d5Vec b ia = 0 := by
         push_neg at h1
         apply d5Vec_apply_other h1.1 h1.2
       rw [hia, mul_zero, zero_add]
       by_cases h2 : ja = ib ∨ ja = jb
       case pos =>
         -- ja hits b. One match => ±2.
         cases h2 with
         | inl hja =>
           rw [hja, d5Vec_apply_i]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
         | inr hja =>
           rw [hja, d5Vec_apply_j]
           rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
           rw [mul_comm]
           nth_rewrite 2 [← one_mul (2:ℝ)]
           apply mul_le_mul_of_nonneg_right
           . simp [sgn]; split_ifs <;> norm_num
           . norm_num
       case neg =>
         -- Neither hits. Inner product 0.
         have hja : d5Vec b ja = 0 := by
            push_neg at h2
            apply d5Vec_apply_other h2.1 h2.2
         rw [hja, mul_zero]
         norm_num

  · intro x hxi hxj
    -- Outside support of a
    rw [d5Vec_apply_other hxi hxj, zero_mul]

-- Lemma 3: Pairwise distance is at least 2
lemma dist_d5Vec_ge_two (a b : D5Index) (hab : a ≠ b) :
    ‖d5Vec a - d5Vec b‖ ≥ 2 := by
  apply dist_ge_two_of_norm_eq_two_and_inner_le_two
  · exact norm_d5Vec a
  · exact norm_d5Vec b
  · exact inner_d5Vec_le_two a b hab



theorem card_pair5 : Fintype.card Pair5 = 10 := by
  native_decide

theorem card_d5_index : Fintype.card D5Index = 40 := by
  simp only [D5Index, Sign2]
  rw [Fintype.card_prod, card_pair5, Fintype.card_prod, Fintype.card_bool]
  try norm_num

theorem exists_kissing_40 : ∃ X : Fin 40 → R5, IsKissingConfiguration 40 X := by
  -- Construct the equivalence
  let d5_equiv : D5Index ≃ Fin 40 :=
    Fintype.equivFinOfCardEq card_d5_index.symm
  let e := d5_equiv.symm
  
  -- Define X
  let X := fun (i : Fin 40) => d5Vec (e i)
  use X
  
  -- Prove IsKissingConfiguration
  constructor
  · intro i
    simp [X]
    apply norm_d5Vec
  · intro i j hij
    simp [X]
    have h_neq : e i ≠ e j := d5_equiv.symm.injective.ne hij
    apply dist_d5Vec_ge_two
    exact h_neq
