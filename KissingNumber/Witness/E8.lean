import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import KissingNumber.Lemmas

open scoped BigOperators RealInnerProductSpace
open Real WithLp

set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unreachableTactic false

/-! ## Computable helpers for inner_root2_bound -/

/-- Parity bit: true iff popcount of 7-bit vector is odd -/
def parityBit (v : Fin 7 → Bool) : Bool :=
  decide ((Finset.univ.filter (fun t => v t)).card % 2 = 1)

/-- Extend 7-bit vector to 8 bits with parity -/
def extBit (v : Fin 7 → Bool) (k : Fin 8) : Bool :=
  if h : (k : ℕ) < 7 then v (Fin.castLT k h) else parityBit v

/-- Signed match sum: +1 per matching coord, -1 per mismatch.
    Equals 4 * ⟪root2 x, root2 y⟫ -/
def sgnMatchSum (x y : Fin 7 → Bool) : ℤ :=
  (Finset.univ : Finset (Fin 8)).sum fun k =>
    if extBit x k == extBit y k then (1 : ℤ) else -1

/-- Combinatorial bound: distinct even-parity vectors differ in ≥ 2 coords -/
lemma sgnMatchSum_le_four_of_ne :
    ∀ (x y : Fin 7 → Bool), x ≠ y → sgnMatchSum x y ≤ 4 := by
  native_decide

noncomputable section

/-! ## Basic Definitions -/

abbrev Pair8 := {p : Fin 8 × Fin 8 // p.1 < p.2}
abbrev Sign2 := Bool × Bool
abbrev Type1Index := Pair8 × Sign2
abbrev Type2Index := Fin 7 → Bool
abbrev E8Index := Sum Type1Index Type2Index

lemma card_type1 : Fintype.card Type1Index = 112 := by native_decide
lemma card_type2 : Fintype.card Type2Index = 128 := by native_decide
lemma card_e8 : Fintype.card E8Index = 240 := by native_decide

def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma sgn_true : sgn true = 1 := rfl
@[simp] lemma sgn_false : sgn false = -1 := rfl
lemma sgn_abs (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]
lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]
lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

lemma sq_sgn_half (b : Bool) : (sgn b * (1/2 : ℝ)) * (sgn b * (1/2 : ℝ)) = 1/4 := by
  have h : sgn b * sgn b = 1 := sgn_mul_self b
  calc (sgn b * (1/2)) * (sgn b * (1/2)) = (sgn b * sgn b) * (1/2 * (1/2)) := by ring
    _ = 1 * (1/4) := by rw [h]; norm_num
    _ = 1/4 := by ring

/-! ## Root Definitions -/

-- Coordinate accessors
abbrev iCoord (idx : Type1Index) : Fin 8 := idx.1.1.1
abbrev jCoord (idx : Type1Index) : Fin 8 := idx.1.1.2

lemma i_ne_j (idx : Type1Index) : iCoord idx ≠ jCoord idx := ne_of_lt idx.1.2

/-- Type 1 root: Two coordinates are ±1, rest are 0 -/
def root1 (idx : Type1Index) : EuclideanSpace ℝ (Fin 8) :=
  toLp 2 (fun k =>
    if k = iCoord idx then sgn idx.2.1
    else if k = jCoord idx then sgn idx.2.2
    else 0)

/-- Type 2 root: All 8 coordinates are ±1/2, with even parity -/
def root2 (idx : Type2Index) : EuclideanSpace ℝ (Fin 8) :=
  toLp 2 (fun k =>
    let bit7 := (Finset.univ.filter (fun t => idx t)).card % 2 = 1
    let bit := if h : (k : ℕ) < 7 then idx (Fin.castLT k h) else bit7
    sgn bit * (1/2 : ℝ))

def e8_root (idx : E8Index) : EuclideanSpace ℝ (Fin 8) :=
  match idx with | Sum.inl i => root1 i | Sum.inr i => root2 i

def e8_point (idx : E8Index) : EuclideanSpace ℝ (Fin 8) := (Real.sqrt 2) • e8_root idx

/-! ## Coordinate Access Lemmas -/

lemma root1_apply_i (idx : Type1Index) : root1 idx (iCoord idx) = sgn idx.2.1 := by
  simp only [root1, PiLp.toLp_apply]
  simp only [↓reduceIte]

lemma root1_apply_j (idx : Type1Index) : root1 idx (jCoord idx) = sgn idx.2.2 := by
  have h : jCoord idx ≠ iCoord idx := (i_ne_j idx).symm
  simp only [root1, PiLp.toLp_apply]
  simp only [h, ↓reduceIte]

lemma root1_apply_other {idx : Type1Index} {k : Fin 8}
    (hki : k ≠ iCoord idx) (hkj : k ≠ jCoord idx) : root1 idx k = 0 := by
  simp only [root1, PiLp.toLp_apply]
  simp only [hki, hkj, ↓reduceIte]

lemma root2_apply_lt7 (idx : Type2Index) (k : Fin 8) (hk : (k : ℕ) < 7) :
    root2 idx k = sgn (idx (Fin.castLT k hk)) * (1/2 : ℝ) := by
  simp only [root2, PiLp.toLp_apply, hk, ↓reduceDIte]

lemma root2_apply_ge7 (idx : Type2Index) (k : Fin 8) (hk : ¬ (k : ℕ) < 7) :
    root2 idx k = sgn ((Finset.univ.filter (fun t => idx t)).card % 2 = 1) * (1/2 : ℝ) := by
  simp only [root2, PiLp.toLp_apply, hk, ↓reduceDIte]

/-! ## Norm Calculations -/

lemma norm_root1 (idx : Type1Index) : ‖root1 idx‖ = Real.sqrt 2 := by
  have h : ⟪root1 idx, root1 idx⟫ = (2 : ℝ) := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_add_of_pair (iCoord idx) (jCoord idx) (i_ne_j idx)]
    · simp only [root1_apply_i, root1_apply_j, RCLike.inner_apply, conj_trivial]
      have h1 : sgn idx.2.1 ^ 2 = 1 := sgn_sq idx.2.1
      have h2 : sgn idx.2.2 ^ 2 = 1 := sgn_sq idx.2.2
      linarith
    · intro x hxi hxj
      simp only [root1_apply_other hxi hxj, RCLike.inner_apply, conj_trivial, mul_zero]
  rw [norm_eq_sqrt_real_inner, h]

lemma norm_root2 (idx : Type2Index) : ‖root2 idx‖ = Real.sqrt 2 := by
  have h : ⟪root2 idx, root2 idx⟫ = (2 : ℝ) := by
    rw [PiLp.inner_apply]
    have h_term : ∀ k, root2 idx k * root2 idx k = 1/4 := by
      intro k
      by_cases hk : (k : ℕ) < 7
      · rw [root2_apply_lt7 idx k hk]; exact sq_sgn_half _
      · rw [root2_apply_ge7 idx k hk]; exact sq_sgn_half _
    simp only [RCLike.inner_apply, conj_trivial, h_term]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    norm_num
  rw [norm_eq_sqrt_real_inner, h]

lemma norm_e8_root (idx : E8Index) : ‖e8_root idx‖ = Real.sqrt 2 := by
  cases idx with
  | inl i => exact norm_root1 i
  | inr i => exact norm_root2 i

lemma norm_e8_point (idx : E8Index) : ‖e8_point idx‖ = 2 := by
  simp only [e8_point, norm_smul, Real.norm_eq_abs, norm_e8_root]
  rw [abs_of_nonneg (sqrt_nonneg 2)]
  rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2) 2]
  norm_num

/-! ## Inner Product Bounds -/

lemma inner_root1_root1_le_one (x y : Type1Index) (hne : x ≠ y) :
    ⟪root1 x, root1 y⟫ ≤ (1 : ℝ) := by
  rw [PiLp.inner_apply]
  let ix := iCoord x; let jx := jCoord x
  let iy := iCoord y; let jy := jCoord y
  rw [Finset.sum_eq_add_of_pair ix jx (i_ne_j x)]
  swap
  · intro k hki hkj
    simp only [RCLike.inner_apply, conj_trivial, root1_apply_other hki hkj, mul_zero]
  rw [root1_apply_i, root1_apply_j]
  simp only [RCLike.inner_apply, conj_trivial]
  -- Count overlaps between {ix, jx} and {iy, jy}
  by_cases hix_iy : ix = iy
  · -- ix = iy
    by_cases hjx_jy : jx = jy
    · -- Same pair: inner = sgn x.1 * sgn y.1 + sgn x.2 * sgn y.2
      have h_pair_eq : x.1 = y.1 := by
        have : x.1.1 = y.1.1 := Prod.ext hix_iy hjx_jy
        exact Subtype.ext this
      have h_signs_ne : x.2 ≠ y.2 := fun h' => hne (Prod.ext h_pair_eq h')
      have hiy_eq : root1 y iy = sgn y.2.1 := root1_apply_i y
      have hjy_eq : root1 y jy = sgn y.2.2 := root1_apply_j y
      rw [hix_iy, hjx_jy, hiy_eq, hjy_eq]
      have h_signs_ne' : x.2.1 ≠ y.2.1 ∨ x.2.2 ≠ y.2.2 := by
        by_contra hc; push_neg at hc; exact h_signs_ne (Prod.ext hc.1 hc.2)
      rcases h_signs_ne' with hs1 | hs2
      · have hmul : sgn x.2.1 * sgn y.2.1 = -1 := by
          cases hx : x.2.1 <;> cases hy : y.2.1 <;> simp [sgn, hx, hy] at hs1 ⊢
        have hbound : sgn y.2.2 * sgn x.2.2 ≤ 1 := by
          cases y.2.2 <;> cases x.2.2 <;> simp [sgn]
        calc sgn y.2.1 * sgn x.2.1 + sgn y.2.2 * sgn x.2.2
            = sgn x.2.1 * sgn y.2.1 + sgn y.2.2 * sgn x.2.2 := by ring
          _ = -1 + sgn y.2.2 * sgn x.2.2 := by rw [hmul]
          _ ≤ -1 + 1 := by linarith
          _ = 0 := by ring
          _ ≤ 1 := by norm_num
      · have hmul : sgn x.2.2 * sgn y.2.2 = -1 := by
          cases hx : x.2.2 <;> cases hy : y.2.2 <;> simp [sgn, hx, hy] at hs2 ⊢
        have hbound : sgn y.2.1 * sgn x.2.1 ≤ 1 := by
          cases y.2.1 <;> cases x.2.1 <;> simp [sgn]
        calc sgn y.2.1 * sgn x.2.1 + sgn y.2.2 * sgn x.2.2
            = sgn y.2.1 * sgn x.2.1 + sgn x.2.2 * sgn y.2.2 := by ring
          _ = sgn y.2.1 * sgn x.2.1 + (-1) := by rw [hmul]
          _ ≤ 1 + (-1) := by linarith
          _ = 0 := by ring
          _ ≤ 1 := by norm_num
    · -- ix = iy but jx ≠ jy
      by_cases hjx_iy : jx = iy
      · exact (i_ne_j x (hix_iy.trans hjx_iy.symm)).elim
      · have hjx_zero : root1 y jx = 0 := by
          apply root1_apply_other hjx_iy
          intro hjx_jy'; exact hjx_jy hjx_jy'
        have hiy_eq : root1 y iy = sgn y.2.1 := root1_apply_i y
        rw [hix_iy, hiy_eq, hjx_zero]
        ring_nf
        have : sgn y.2.1 * sgn x.2.1 ≤ 1 := by cases x.2.1 <;> cases y.2.1 <;> simp [sgn]
        linarith
  · -- ix ≠ iy
    by_cases hix_jy : ix = jy
    · -- ix = jy
      by_cases hjx_iy : jx = iy
      · -- Cross match: ix = jy, jx = iy contradicts ordering
        have h1 : (ix : ℕ) < (jx : ℕ) := x.1.2
        have h2 : (iy : ℕ) < (jy : ℕ) := y.1.2
        have : (jy : ℕ) < (iy : ℕ) := by rw [← hix_jy, ← hjx_iy]; exact h1
        omega
      · -- ix = jy but jx ≠ iy
        by_cases hjx_jy : jx = jy
        · exact (i_ne_j x (hix_jy.trans hjx_jy.symm)).elim
        · have hjx_zero : root1 y jx = 0 := root1_apply_other hjx_iy hjx_jy
          have hjy_eq : root1 y jy = sgn y.2.2 := root1_apply_j y
          rw [hix_jy, hjy_eq, hjx_zero]
          ring_nf
          have : sgn y.2.2 * sgn x.2.1 ≤ 1 := by cases x.2.1 <;> cases y.2.2 <;> simp [sgn]
          linarith
    · -- ix ≠ iy and ix ≠ jy, so root1 y ix = 0
      have hix_zero : root1 y ix = 0 := root1_apply_other hix_iy hix_jy
      by_cases hjx_iy : jx = iy
      · have hiy_eq : root1 y iy = sgn y.2.1 := root1_apply_i y
        rw [hix_zero, hjx_iy, hiy_eq]
        ring_nf
        have : sgn y.2.1 * sgn x.2.2 ≤ 1 := by cases x.2.2 <;> cases y.2.1 <;> simp [sgn]
        linarith
      · by_cases hjx_jy : jx = jy
        · have hjy_eq : root1 y jy = sgn y.2.2 := root1_apply_j y
          rw [hix_zero, hjx_jy, hjy_eq]
          ring_nf
          have : sgn y.2.2 * sgn x.2.2 ≤ 1 := by cases x.2.2 <;> cases y.2.2 <;> simp [sgn]
          linarith
        · have hjx_zero : root1 y jx = 0 := root1_apply_other hjx_iy hjx_jy
          rw [hix_zero, hjx_zero]
          ring_nf
          norm_num

/-- Each root2 coordinate equals sgn(extBit) * 1/2 -/
private lemma root2_coord_eq (x : Type2Index) (k : Fin 8) :
    root2 x k = sgn (extBit x k) * (1/2 : ℝ) := by
  by_cases hk : (k : ℕ) < 7
  · rw [root2_apply_lt7 x k hk]
    simp only [extBit, hk, dite_true]
  · rw [root2_apply_ge7 x k hk]
    simp only [extBit, hk, dite_false, parityBit]

/-- Coordinate product of two root2 vectors -/
private lemma root2_mul_eq (x y : Type2Index) (k : Fin 8) :
    root2 x k * root2 y k =
      (if extBit x k == extBit y k then (1:ℝ) else -1) / 4 := by
  rw [root2_coord_eq x k, root2_coord_eq y k]
  cases extBit x k <;> cases extBit y k <;> simp [sgn] <;> ring

/-- Inner product equals sgnMatchSum / 4 -/
private lemma inner_root2_eq (x y : Type2Index) :
    ⟪root2 x, root2 y⟫ = (sgnMatchSum x y : ℝ) / 4 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [show (4:ℝ) = 4 from rfl]
  simp only [sgnMatchSum]
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [root2_mul_eq]
  push_cast
  cases extBit x k <;> cases extBit y k <;> simp

/-- The inner product of distinct Type 2 roots is at most 1 -/
lemma inner_root2_bound (x y : Type2Index) (hne : x ≠ y) :
    ⟪root2 x, root2 y⟫ ≤ (1 : ℝ) := by
  rw [inner_root2_eq]
  have h := sgnMatchSum_le_four_of_ne x y hne
  have h4 : (sgnMatchSum x y : ℝ) ≤ 4 := by exact_mod_cast h
  linarith

lemma inner_root2_root2_le_one (x y : Type2Index) (h : x ≠ y) :
    ⟪root2 x, root2 y⟫ ≤ (1 : ℝ) := inner_root2_bound x y h

lemma inner_root1_root2_le_one (x : Type1Index) (y : Type2Index) :
    ⟪root1 x, root2 y⟫ ≤ (1 : ℝ) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  let ix := iCoord x; let jx := jCoord x
  rw [Finset.sum_eq_add_of_pair ix jx (i_ne_j x)]
  swap
  · intro k hki hkj
    simp only [root1_apply_other hki hkj, mul_zero]
  rw [root1_apply_i, root1_apply_j]
  have hb : ∀ k, |root2 y k| ≤ 1/2 := by
    intro k
    by_cases hk : (k : ℕ) < 7
    · rw [root2_apply_lt7 y k hk]; simp [abs_mul, sgn_abs]
    · rw [root2_apply_ge7 y k hk]; simp [abs_mul, sgn_abs]
  -- The sum is root2 y ix * sgn x.2.1 + root2 y jx * sgn x.2.2
  have habs_le : root2 y ix * sgn x.2.1 + root2 y jx * sgn x.2.2
      ≤ |root2 y ix * sgn x.2.1| + |root2 y jx * sgn x.2.2| := by
    have h1 : root2 y ix * sgn x.2.1 ≤ |root2 y ix * sgn x.2.1| := le_abs_self _
    have h2 : root2 y jx * sgn x.2.2 ≤ |root2 y jx * sgn x.2.2| := le_abs_self _
    linarith
  calc root2 y ix * sgn x.2.1 + root2 y jx * sgn x.2.2
      ≤ |root2 y ix * sgn x.2.1| + |root2 y jx * sgn x.2.2| := habs_le
    _ = |root2 y ix| * |sgn x.2.1| + |root2 y jx| * |sgn x.2.2| := by simp [abs_mul]
    _ = |root2 y ix| + |root2 y jx| := by simp [sgn_abs]
    _ ≤ 1/2 + 1/2 := by linarith [hb ix, hb jx]
    _ = 1 := by ring

lemma inner_root_le_one (x y : E8Index) (h : x ≠ y) :
    ⟪e8_root x, e8_root y⟫ ≤ (1 : ℝ) := by
  cases x with
  | inl x1 =>
    cases y with
    | inl y1 =>
      simp only [e8_root]
      apply inner_root1_root1_le_one
      intro heq; apply h; simp [heq]
    | inr y2 =>
      simp only [e8_root]
      apply inner_root1_root2_le_one
  | inr x2 =>
    cases y with
    | inl y1 =>
      simp only [e8_root]
      rw [real_inner_comm]
      exact inner_root1_root2_le_one y1 x2
    | inr y2 =>
      simp only [e8_root]
      apply inner_root2_root2_le_one
      intro heq; apply h; simp [heq]

/-! ## Main Theorem -/

lemma inner_e8_smul_smul (a : ℝ) (u v : EuclideanSpace ℝ (Fin 8)) :
    ⟪a • u, a • v⟫ = a^2 * ⟪u, v⟫ := by
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

theorem exists_kissing_240 :
    ∃ X : Fin 240 → EuclideanSpace ℝ (Fin 8),
      (∀ i, ‖X i‖ = 2) ∧ (∀ i j, i ≠ j → ‖X i - X j‖ ≥ 2) := by
  let equiv : E8Index ≃ Fin 240 := Fintype.equivFinOfCardEq card_e8
  let X := fun i => e8_point (equiv.symm i)
  refine ⟨X, ?_, ?_⟩
  · intro i; exact norm_e8_point (equiv.symm i)
  · intro i j hne
    let u := equiv.symm i
    let v := equiv.symm j
    have huv : u ≠ v := equiv.symm.injective.ne hne
    have hroot : ⟪e8_root u, e8_root v⟫ ≤ (1 : ℝ) := inner_root_le_one u v huv
    have hscaled : ⟪e8_point u, e8_point v⟫ ≤ (2 : ℝ) := by
      simp only [e8_point]
      rw [inner_e8_smul_smul]
      have hs : Real.sqrt 2 ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      rw [hs]; linarith
    apply dist_ge_two_of_norm_eq_two_and_inner_le_two
    · exact norm_e8_point u
    · exact norm_e8_point v
    · exact hscaled

end
