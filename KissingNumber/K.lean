import KissingNumber.Defs

namespace KissingNumber

/-- The set of admissible configuration sizes in dimension n. -/
def admissible (n : ℕ) : Set ℕ :=
  {N | ∃ X : Fin N → EuclideanSpace ℝ (Fin n), IsKissingConfiguration n N X}

/-- The kissing number in dimension n, as a supremum in ℕ∞ = WithTop ℕ.
    This avoids needing an upper bound to define the value. -/
noncomputable def K (n : ℕ) : WithTop ℕ :=
  sSup ((fun N : ℕ => (N : WithTop ℕ)) '' admissible n)

/-- Any witness configuration gives a lower bound on K. -/
theorem le_K_of_exists {n N : ℕ}
    (h : ∃ X : Fin N → EuclideanSpace ℝ (Fin n), IsKissingConfiguration n N X) :
    (N : WithTop ℕ) ≤ K n :=
  le_sSup ⟨N, h, rfl⟩

end KissingNumber
