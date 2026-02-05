import KissingNumber.Defs
import KissingNumber.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real

/--
D3 Index: a pair of distinct coordinates in Fin 3 and two signs.
Pairs: (0,1), (0,2), (1,2) -> 3 pairs.
Signs: (±1, ±1) -> 4 combinations.
Total: 3 * 4 = 12 points.
-/
abbrev Pair3 := {p : Fin 3 × Fin 3 // p.1 < p.2}
abbrev D3Index := Pair3 × (Bool × Bool)

noncomputable def sgn (b : Bool) : ℝ := if b then (1:ℝ) else (-1)

/--
The 12 vertices of the cuboctahedron (scaled D3 roots).
Each vector has two coordinates as ±√2 and one as 0.
Norm squared = 2 + 2 = 4, so Norm = 2.
-/
noncomputable def d3Vec (idx : D3Index) : EuclideanSpace ℝ (Fin 3) :=
  let i := idx.1.1.1
  let j := idx.1.1.2
  let si := sgn idx.2.1
  let sj := sgn idx.2.2
  fun k =>
    if k = i then si * Real.sqrt 2
    else if k = j then sj * Real.sqrt 2
    else 0

lemma sgn_sq (b : Bool) : (sgn b)^2 = 1 := by
  cases b <;> simp [sgn]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

-- Coordinate helpers
abbrev iCoord (idx : D3Index) : Fin 3 := idx.1.1.1
abbrev jCoord (idx : D3Index) : Fin 3 := idx.1.1.2

lemma i_ne_j (idx : D3Index) : iCoord idx ≠ jCoord idx :=
  ne_of_lt idx.1.2

lemma d3Vec_apply_i (idx : D3Index) : d3Vec idx (iCoord idx) = sgn idx.2.1 * Real.sqrt 2 := by
  simp [d3Vec, iCoord, jCoord, i_ne_j]

lemma d3Vec_apply_j (idx : D3Index) : d3Vec idx (jCoord idx) = sgn idx.2.2 * Real.sqrt 2 := by
  let i := iCoord idx
  let j := jCoord idx
  have h : j ≠ i := (i_ne_j idx).symm
  simp [d3Vec, iCoord, jCoord, h]

lemma d3Vec_apply_other {idx : D3Index} {k : Fin 3} (hki : k ≠ iCoord idx) (hkj : k ≠ jCoord idx) :
    d3Vec idx k = 0 := by
  simp [d3Vec, iCoord, jCoord, hki, hkj]

/-- All vectors lie on the sphere of radius 2. -/
lemma norm_d3Vec (idx : D3Index) : ‖d3Vec idx‖ = 2 := by
  have h : ⟪d3Vec idx, d3Vec idx⟫_ℝ = 4 := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_add_of_mem (Finset.mem_univ (iCoord idx)) (Finset.mem_univ (jCoord idx)) (i_ne_j idx)]
    · simp [d3Vec_apply_i, d3Vec_apply_j, sgn_sq]
      ring
    · intro x hxi hxj
      simp [d3Vec_apply_other hxi hxj]
  exact Real.norm_of_inner_self_eq_sq (by norm_num) h

/-- Inner product of distinct vectors is at most 2. -/
lemma inner_d3Vec_le_two (a b : D3Index) (hab : a ≠ b) :
    ⟪d3Vec a, d3Vec b⟫_ℝ ≤ 2 := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_add_of_mem (Finset.mem_univ (iCoord a)) (Finset.mem_univ (jCoord a)) (i_ne_j a)]
  · rw [d3Vec_apply_i, d3Vec_apply_j]
    let ia := iCoord a; let ja := jCoord a
    let ib := iCoord b; let jb := jCoord b
    by_cases h1 : ia = ib ∨ ia = jb
    case pos =>
      by_cases h2 : ja = ib ∨ ja = jb
      case pos =>
        -- Same support pair => must differ in signs
        have h_pair_eq : a.1 = b.1 := by
          cases h1 with h1l h1r <;> cases h2 with h2l h2r
          · subst h1l; subst h2l; exact (i_ne_j a rfl).elim
          · ext; exact h1l; exact h2r
          · have : ia < ja := a.1.2; have : ib < jb := b.1.2
            subst h1r; subst h2l; linarith
          · subst h1r; subst h2r; exact (i_ne_j a rfl).elim
        
        have h_signs_ne : a.2 ≠ b.2 := by
          intro h; apply hab; ext <;> assumption
        
        rw [h_pair_eq] at *
        rw [d3Vec_apply_i, d3Vec_apply_j]
        -- sgn a.i * sgn b.i * 2 + sgn a.j * sgn b.j * 2
        -- At least one sign differs, so sum is 0 or -4.
        replace h_signs_ne : a.2.1 ≠ b.2.1 ∨ a.2.2 ≠ b.2.2 := by
          contrapose! h_signs_ne; ext <;> assumption
        
        cases h_signs_ne with hs1 hs2
        · -- Sign 1 differs
          have : sgn a.2.1 * sgn b.2.1 = -1 := by
            cases a.2.1 <;> cases b.2.1 <;> simp [sgn] at *; assumption; assumption
          simp [this]; nlinarith [sgn_abs a.2.2, sgn_abs b.2.2]
        · -- Sign 2 differs
          have : sgn a.2.2 * sgn b.2.2 = -1 := by
            cases a.2.2 <;> cases b.2.2 <;> simp [sgn] at *; assumption; assumption
          simp [this]; nlinarith [sgn_abs a.2.1, sgn_abs b.2.1]
          
      case neg =>
        -- ia matches, ja matches nothing in b. Inner product is ±2.
        have hja : d3Vec b ja = 0 := by
          push_neg at h2; apply d3Vec_apply_other h2.1 h2.2
        rw [hja, mul_zero, add_zero]
        cases h1 with | inl h => rw [h, d3Vec_apply_i] | inr h => rw [h, d3Vec_apply_j]
        rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
        have : sgn a.2.1 * sgn _ ≤ 1 := by cases a.2.1 <;> cases _ <;> simp [sgn] <;> norm_num
        nlinarith
        
    case neg =>
      by_cases h2 : ja = ib ∨ ja = jb
      case pos =>
        -- ja matches, ia matches nothing. Inner product ±2.
        have hia : d3Vec b ia = 0 := by
          push_neg at h1; apply d3Vec_apply_other h1.1 h1.2
        rw [hia, mul_zero, zero_add]
        cases h2 with | inl h => rw [h, d3Vec_apply_i] | inr h => rw [h, d3Vec_apply_j]
        rw [← mul_assoc, mul_comm (Real.sqrt 2), mul_assoc (Real.sqrt 2), Real.mul_self_sqrt (by norm_num)]
        have : sgn a.2.2 * sgn _ ≤ 1 := by cases a.2.2 <;> cases _ <;> simp [sgn] <;> norm_num
        nlinarith
      case neg =>
        -- No matches. Inner product 0.
        have hia : d3Vec b ia = 0 := by push_neg at h1; apply d3Vec_apply_other h1.1 h1.2
        have hja : d3Vec b ja = 0 := by push_neg at h2; apply d3Vec_apply_other h2.1 h2.2
        rw [hia, hja]; norm_num
  · intro x hxi hxj
    simp [d3Vec_apply_other hxi hxj]

theorem card_pair3 : Fintype.card Pair3 = 3 := by
  native_decide

theorem card_d3_index : Fintype.card D3Index = 12 := by
  simp [card_pair3]

theorem exists_kissing_12 : ∃ X : Fin 12 → EuclideanSpace ℝ (Fin 3), IsKissingConfiguration 3 12 X := by
  let e := Fintype.equivFinOfCardEq card_d3_index.symm
  let X := fun i => d3Vec (e.symm i)
  apply kissing_config_of_inner_le_two X
  · intro i; simp [X]; apply norm_d3Vec
  · intro i j hij; simp [X]
    apply inner_d3Vec_le_two
    exact e.symm.injective.ne hij
