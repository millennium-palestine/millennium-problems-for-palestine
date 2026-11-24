import Mathlib

namespace MPP.Solutions.Bsd098

theorem main : ∀ n : ℕ, {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
    Rat.HeightOneSpectrum.natGenerator v ≤ n}.Finite := by
  intro n
  have hT : {p : Nat.Primes | (p : ℕ) ≤ n}.Finite :=
    (Set.finite_Iic n).preimage Subtype.val_injective.injOn
  have h2 := hT.preimage (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).injective.injOn
  convert h2 using 1
  ext v
  simp [Rat.HeightOneSpectrum.primesEquiv]

end MPP.Solutions.Bsd098
