import Mathlib

namespace MPP.Solutions.Bsd182

theorem main : ∀ (K : Type) [Field K] (p J N : ℕ), 0 < p → N ≤ p →
    LinearIndependent K (fun u : Fin J × Fin N => (Polynomial.X : Polynomial K) ^ (p * (u.1 : ℕ) + (u.2 : ℕ))) := by
  intro K _ p J N hp hN
  have hinj : Function.Injective (fun u : Fin J × Fin N => p * (u.1 : ℕ) + (u.2 : ℕ)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only at h
    have hb : (b : ℕ) < p := lt_of_lt_of_le b.isLt hN
    have hb' : (b' : ℕ) < p := lt_of_lt_of_le b'.isLt hN
    have hmod : (b : ℕ) = (b' : ℕ) := by
      have h1 := congrArg (· % p) h
      simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] using h1
    rw [hmod] at h
    have h2 : p * (a : ℕ) = p * (a' : ℕ) := Nat.add_right_cancel h
    have hdiv : (a : ℕ) = (a' : ℕ) := Nat.eq_of_mul_eq_mul_left hp h2
    exact Prod.ext (Fin.ext hdiv) (Fin.ext hmod)
  have hli := (Polynomial.basisMonomials K).linearIndependent.comp _ hinj
  simpa [Function.comp_def, Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial] using hli

end MPP.Solutions.Bsd182
