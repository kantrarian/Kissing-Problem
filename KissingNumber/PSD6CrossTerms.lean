import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

/-!
# PSD Cross-Terms for k=6

Feature map: phi6 = A6 - (1/16)*B6 + (1/224)*C6 - (1/2688)*D6
Kernel: ∑ phi6(x,p)*phi6(y,p) = (231/896) * P8 6 ⟪x,y⟫

Components (for 6-tuple p = (a,b,c,d,e,f)):
- A6: x(a)x(b)x(c)x(d)x(e)x(f)                    — 1 term
- B6: ∑ δ_{pair} * x(remaining 4)                   — 15 terms [C(6,2)]
- C6: ∑ x(pair) * δ_{double-pair}(remaining 4)      — 45 terms [C(6,2)*3]
- D6: ∑ δ_{triple-pair}                             — 15 terms [5!!]
-/

-- Type alias for 6-tuples
private abbrev T6 := Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8

/-! ## Helper lemmas (shared with PSD5CrossTerms) -/

private lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

private lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]; congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

-- Iterated sum lemma for ∑ over Fin 8 with delta = sum_ite_const_zero
private lemma sum_ite_const_zero {f : Fin 8 → ℝ} :
    ∀ a : Fin 8, ∑ b : Fin 8, (if a = b then f b else 0) = f a :=
  fun a => by simp [Finset.sum_ite_eq, Finset.mem_univ]

-- Pull a constant conditional out of a sum
private lemma sum_ite_prop_zero {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

-- Factor 2-fold sum: ∑_a ∑_b f(a)*g(b) = (∑_a f a) * (∑_b g b)
private lemma factor2 (f g : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, f a * g b =
    (∑ a, f a) * (∑ b, g b) := by
  rw [Finset.sum_mul]; congr 1; ext a; rw [← Finset.mul_sum]

-- Factor 3-fold sum
private lemma factor3 (f g h : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, f a * g b * h c =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

-- Factor 4-fold sum
private lemma factor4 (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, f a * g b * h c * j d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

-- Factor 5-fold sum
private lemma factor5 (f g h j k : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8,
    f a * g b * h c * j d * k e =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) * (∑ e, k e) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

/-! ## Definitions -/

-- A6: raw 6th moment tensor (1 term)
private def A6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2.1 * x p.2.2.2.1 * x p.2.2.2.2.1 * x p.2.2.2.2.2

-- B6: single-delta correction (15 terms = C(6,2) pairs)
-- Each pair (i,j) contributes δ_{pi pj} * product of x at remaining 4 positions
private def B6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  -- 15 terms: one for each pair from {a,b,c,d,e,f}
  (if a = b then 1 else 0) * x c * x d * x e * x f
  + (if a = c then 1 else 0) * x b * x d * x e * x f
  + (if a = d then 1 else 0) * x b * x c * x e * x f
  + (if a = e then 1 else 0) * x b * x c * x d * x f
  + (if a = f then 1 else 0) * x b * x c * x d * x e
  + (if b = c then 1 else 0) * x a * x d * x e * x f
  + (if b = d then 1 else 0) * x a * x c * x e * x f
  + (if b = e then 1 else 0) * x a * x c * x d * x f
  + (if b = f then 1 else 0) * x a * x c * x d * x e
  + (if c = d then 1 else 0) * x a * x b * x e * x f
  + (if c = e then 1 else 0) * x a * x b * x d * x f
  + (if c = f then 1 else 0) * x a * x b * x d * x e
  + (if d = e then 1 else 0) * x a * x b * x c * x f
  + (if d = f then 1 else 0) * x a * x b * x c * x e
  + (if e = f then 1 else 0) * x a * x b * x c * x d

-- C6: double-delta correction (45 terms = C(6,2)*3)
-- Choose 2 x-positions from 6, partition remaining 4 into 2 delta-pairs (3 ways)
private def C6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  -- x at {a,b}, deltas on {c,d,e,f}: 3 pairings
  x a * x b * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  -- x at {a,c}, deltas on {b,d,e,f}
  + x a * x c * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  -- x at {a,d}, deltas on {b,c,e,f}
  + x a * x d * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  -- x at {a,e}, deltas on {b,c,d,f}
  + x a * x e * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  -- x at {a,f}, deltas on {b,c,d,e}
  + x a * x f * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))
  -- x at {b,c}, deltas on {a,d,e,f}
  + x b * x c * ((if a=d then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if d=f then 1 else 0) + (if a=f then 1 else 0)*(if d=e then 1 else 0))
  -- x at {b,d}, deltas on {a,c,e,f}
  + x b * x d * ((if a=c then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=e then 1 else 0))
  -- x at {b,e}, deltas on {a,c,d,f}
  + x b * x e * ((if a=c then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=d then 1 else 0))
  -- x at {b,f}, deltas on {a,c,d,e}
  + x b * x f * ((if a=c then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if c=e then 1 else 0) + (if a=e then 1 else 0)*(if c=d then 1 else 0))
  -- x at {c,d}, deltas on {a,b,e,f}
  + x c * x d * ((if a=b then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=e then 1 else 0))
  -- x at {c,e}, deltas on {a,b,d,f}
  + x c * x e * ((if a=b then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=d then 1 else 0))
  -- x at {c,f}, deltas on {a,b,d,e}
  + x c * x f * ((if a=b then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=d then 1 else 0))
  -- x at {d,e}, deltas on {a,b,c,f}
  + x d * x e * ((if a=b then 1 else 0)*(if c=f then 1 else 0) + (if a=c then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=c then 1 else 0))
  -- x at {d,f}, deltas on {a,b,c,e}
  + x d * x f * ((if a=b then 1 else 0)*(if c=e then 1 else 0) + (if a=c then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=c then 1 else 0))
  -- x at {e,f}, deltas on {a,b,c,d}
  + x e * x f * ((if a=b then 1 else 0)*(if c=d then 1 else 0) + (if a=c then 1 else 0)*(if b=d then 1 else 0) + (if a=d then 1 else 0)*(if b=c then 1 else 0))

-- D6: triple-delta (15 terms = 5!! ways to partition 6 positions into 3 pairs)
private def D6 (_x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  -- 15 = 5!! partitions of {a,b,c,d,e,f} into 3 pairs
  -- Group by first pair containing 'a':
  -- a paired with b: (ab)(cd)(ef), (ab)(ce)(df), (ab)(cf)(de) = 3 terms
  (if a=b then 1 else 0) * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  -- a paired with c: (ac)(bd)(ef), (ac)(be)(df), (ac)(bf)(de) = 3 terms
  + (if a=c then 1 else 0) * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  -- a paired with d: (ad)(bc)(ef), (ad)(be)(cf), (ad)(bf)(ce) = 3 terms
  + (if a=d then 1 else 0) * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  -- a paired with e: (ae)(bc)(df), (ae)(bd)(cf), (ae)(bf)(cd) = 3 terms
  + (if a=e then 1 else 0) * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  -- a paired with f: (af)(bc)(de), (af)(bd)(ce), (af)(be)(cd) = 3 terms
  + (if a=f then 1 else 0) * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))

-- ============================================================
-- Feature map definition
-- ============================================================

private def phi6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  A6 x p - (1 : ℝ) / 16 * B6 x p + (1 : ℝ) / 224 * C6 x p - (1 : ℝ) / 2688 * D6 x p

private lemma phi6_product (x y : EuclideanSpace ℝ (Fin 8)) (p : T6) :
    phi6 x p * phi6 y p =
    A6 x p * A6 y p
    - (1/16) * (A6 x p * B6 y p + B6 x p * A6 y p)
    + (1/224) * (A6 x p * C6 y p + C6 x p * A6 y p)
    - (1/2688) * (A6 x p * D6 y p + D6 x p * A6 y p)
    + (1/256) * (B6 x p * B6 y p)
    - (1/3584) * (B6 x p * C6 y p + C6 x p * B6 y p)
    + (1/43008) * (B6 x p * D6 y p + D6 x p * B6 y p)
    + (1/50176) * (C6 x p * C6 y p)
    - (1/602112) * (C6 x p * D6 y p + D6 x p * C6 y p)
    + (1/7225344) * (D6 x p * D6 y p) := by
  simp only [phi6]; ring

-- ============================================================
-- Cross-term sum lemmas
-- ============================================================

-- sum_AA: ∑ A6(x,p)*A6(y,p) = s^6
private lemma sum_AA (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : T6, A6 x p * A6 y p =
    (@inner ℝ _ _ x y) ^ 6 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [A6]
  simp_rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d; arg 2; ext e
    rw [show ∑ f : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e * y.ofLp f) =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) * ∑ f, x.ofLp f * y.ofLp f
        from by rw [Finset.mul_sum]; congr 1; ext f; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
    rw [show ∑ e : Fin 8,
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) * s =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * s * ∑ e, x.ofLp e * y.ofLp e
        from by rw [Finset.mul_sum]; congr 1; ext e; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b; arg 2; ext c
    rw [show ∑ d : Fin 8,
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * s * s =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        s * s * ∑ d, x.ofLp d * y.ofLp d
        from by rw [Finset.mul_sum]; congr 1; ext d; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a; arg 2; ext b
    rw [show ∑ c : Fin 8,
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        s * s * s =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * s^3 * ∑ c, x.ofLp c * y.ofLp c
        from by rw [Finset.mul_sum]; congr 1; ext c; ring]
  simp_rw [← hs]
  conv_lhs =>
    arg 2; ext a
    rw [show ∑ b : Fin 8,
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * s ^ 3 * s =
        (x.ofLp a * y.ofLp a) * s^4 * ∑ b, x.ofLp b * y.ofLp b
        from by rw [Finset.mul_sum]; congr 1; ext b; ring]
  simp_rw [← hs]
  rw [show ∑ a : Fin 8, x.ofLp a * y.ofLp a * s ^ 4 * s =
      (∑ a, x.ofLp a * y.ofLp a) * s^5 from by rw [Finset.sum_mul]; congr 1; ext a; ring]
  rw [← hs]; ring

-- sum_AB: ∑ A6(x,p)*B6(y,p) = 15*s^4
set_option maxHeartbeats 25600000 in
private lemma sum_AB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6, A6 x p * B6 y p =
    15 * (@inner ℝ _ _ x y) ^ 4 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A6, B6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 8000000 }) only [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- After delta collapse: 15 five-fold sums. Rearrange to factor5-compatible form.
  -- x_1 doubled (5 terms):
  have r1 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r2 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp e * (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r3 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp e * (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r4 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp e * (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r5 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp a * (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  -- x_2 doubled (4 terms):
  have r6 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r7 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp e * (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r8 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp e * (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r9 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp b * (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  -- x_3 doubled (3 terms):
  have r10 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp e * (y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r11 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp e * (y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r12 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp c * (y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  -- x_4 doubled (2 terms):
  have r13 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp e * (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * x.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r14 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp d * (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp e) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * x.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  -- x_5 doubled (1 term):
  have r15 : ∀ a b c d e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp e * (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * x.ofLp e) := by intros; ring
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, factor5, hxn, ← hs]
  ring

-- sum_BA by symmetry
private lemma sum_BA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : T6, B6 x p * A6 y p = 15 * (@inner ℝ _ _ x y) ^ 4 := by
  simp_rw [show ∀ p, B6 x p * A6 y p = A6 y p * B6 x p from fun p => mul_comm _ _]
  rw [sum_AB y x hy, real_inner_comm y x]

-- sum_AC: ∑ A6(x,p)*C6(y,p) = 45*s^2
set_option maxHeartbeats 51200000 in
private lemma sum_AC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6, A6 x p * C6 y p =
    45 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A6, C6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 30000000 }) only [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Normalize x ^ 2 back to x * x (delta collapse introduces ^ 2)
  simp only [sq]
  -- 41 unique rearrangement lemmas for the 45 four-fold sums
  have r1 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r2 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r3 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r4 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r5 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r6 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r7 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r8 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r9 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r10 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r11 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r12 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r13 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r14 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r15 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r16 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r17 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r18 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r19 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r20 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r21 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r22 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r23 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r24 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r25 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r26 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r27 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r28 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r29 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r30 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r31 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r32 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r33 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r34 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r35 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r36 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r37 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r38 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r39 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp a * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r40 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r41 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, factor4, hxn, ← hs]
  ring

private lemma sum_CA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : T6, C6 x p * A6 y p = 45 * (@inner ℝ _ _ x y) ^ 2 := by
  simp_rw [show ∀ p, C6 x p * A6 y p = A6 y p * C6 x p from fun p => mul_comm _ _]
  rw [sum_AC y x hy, real_inner_comm y x]

-- sum_AD: ∑ A6(x,p)*D6(y,p) = 15
-- D6 has no x dependence, so this is (∑ x_a^2)^3 * (number of terms) = 15
set_option maxHeartbeats 25600000 in
private lemma sum_AD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6, A6 x p * D6 y p = 15 := by
  have hxn := ofLp_norm_sq x hx
  simp only [A6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 8000000 }) only [mul_add, Finset.sum_add_distrib]
  -- Step 1: handle ite multiplication
  simp only [mul_ite, mul_zero, mul_one]
  -- Step 2: first delta collapse (innermost sums)
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 3: pull constant ifs outside, collapse again
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 4: repeat
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Now 1 + 14 triple sums = 15. Each sum's product is a permutation of x_a²*x_b²*x_c².
  -- Rewrite all 15 orderings to grouped form, then factor and substitute.
  have r0 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r1 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r2 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r3 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r4 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r5 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r6 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r7 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp b * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r8 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r9 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r10 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp a * x.ofLp c = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r11 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r12 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r13 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r14 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  simp_rw [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, factor3, hxn]
  norm_num

private lemma sum_DA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : T6, D6 x p * A6 y p = 15 := by
  simp_rw [show ∀ p, D6 x p * A6 y p = A6 y p * D6 x p from fun p => mul_comm _ _]
  exact sum_AD y x hy

-- sum_BB: ∑ B6(x,p)*B6(y,p) = 240*s^4 + 90*s^2
private lemma sum_BB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, B6 x p * B6 y p =
    240 * (@inner ℝ _ _ x y) ^ 4 + 90 * (@inner ℝ _ _ x y) ^ 2 := by
  sorry

-- sum_BC: ∑ B6(x,p)*C6(y,p) = 1260*s^2 + 45
private lemma sum_BC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, B6 x p * C6 y p =
    1260 * (@inner ℝ _ _ x y) ^ 2 + 45 := by
  sorry

private lemma sum_CB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, C6 x p * B6 y p =
    1260 * (@inner ℝ _ _ x y) ^ 2 + 45 := by
  simp_rw [show ∀ p, C6 x p * B6 y p = B6 y p * C6 x p from fun p => mul_comm _ _]
  rw [sum_BC y x hy hx, real_inner_comm y x]

-- sum_BD: ∑ B6(x,p)*D6(y,p) = 540 (constant; D6 has no y-dependence)
set_option maxHeartbeats 800000000 in
private lemma sum_BD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, B6 x p * D6 y p =
    (540 : ℝ) := by
  have hxn := ofLp_norm_sq x hx
  simp only [B6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 200000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have r1 : ∀ a b : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r3 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, factor2, hxn]
  norm_num

private lemma sum_DB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, D6 x p * B6 y p =
    (540 : ℝ) := by
  simp_rw [show ∀ p, D6 x p * B6 y p = B6 y p * D6 x p from fun p => mul_comm _ _]
  exact sum_BD y x hy hx

-- sum_CC: ∑ C6(x,p)*C6(y,p) = 7560*s^2 + 1080
private lemma sum_CC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, C6 x p * C6 y p =
    7560 * (@inner ℝ _ _ x y) ^ 2 + 1080 := by
  sorry

-- sum_CD: ∑ C6(x,p)*D6(y,p) = 5400 (constant; D6 has no y-dependence)
set_option maxHeartbeats 1600000000 in
private lemma sum_CD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, C6 x p * D6 y p =
    (5400 : ℝ) := by
  have hxn := ofLp_norm_sq x hx
  simp only [C6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- After full collapse, we have single sums ∑_a x_a² = 1
  simp_rw [hxn]
  norm_num

private lemma sum_DC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, D6 x p * C6 y p =
    (5400 : ℝ) := by
  simp_rw [show ∀ p, D6 x p * C6 y p = C6 y p * D6 x p from fun p => mul_comm _ _]
  exact sum_CD y x hy hx

-- sum_DD: D6 doesn't depend on x,y, only on p. ∑_p D6(p)^2 = 14400.
set_option maxHeartbeats 400000000 in
private lemma sum_DD (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : T6, D6 x p * D6 y p = 14400 := by
  simp only [D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 100000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 100000000 }) only [mul_ite, mul_zero, mul_one]
  simp (config := { maxSteps := 100000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 100000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 100000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 100000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 100000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  norm_num

-- ============================================================
-- Main kernel identity
-- ============================================================

private lemma phi6_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, phi6 x p * phi6 y p =
    (231 : ℝ) / 896 * P8 6 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : T6, phi6 x p * phi6 y p =
      (@inner ℝ _ _ x y) ^ 6 - 15 / 16 * (@inner ℝ _ _ x y) ^ 4
      + 45 / 224 * (@inner ℝ _ _ x y) ^ 2 - 5 / 896 by
    rw [h, P8_6]; ring
  set s := @inner ℝ _ _ x y
  simp_rw [phi6_product]
  simp only [sub_eq_add_neg]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [sum_AA, sum_AB x y hx, sum_BA x y hy, sum_AC x y hx, sum_CA x y hy,
      sum_AD x y hx, sum_DA x y hy,
      sum_BB x y hx hy, sum_BC x y hx hy, sum_CB x y hx hy,
      sum_BD x y hx hy, sum_DB x y hx hy,
      sum_CC x y hx hy, sum_CD x y hx hy, sum_DC x y hx hy,
      sum_DD]
  ring

-- ============================================================
-- Public exports for use by PSD.lean
-- ============================================================

def phi6Feature (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  phi6 x p

lemma phi6Feature_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6, phi6Feature x p * phi6Feature y p =
    (231 : ℝ) / 896 * P8 6 (@inner ℝ _ _ x y) := by
  simp only [phi6Feature]
  exact phi6_kernel x y hx hy

end
