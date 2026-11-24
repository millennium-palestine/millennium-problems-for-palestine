import Mathlib

namespace MPP.Solutions.Bsd099

theorem main : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) =
      Rat.HeightOneSpectrum.natGenerator v := by
  intro v
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    (R := NumberField.RingOfIntegers ℚ) v
  calc Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
      = Nat.card (IsLocalRing.ResidueField (PadicInt (Rat.HeightOneSpectrum.primesEquiv v : ℕ))) :=
        Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e.toRingEquiv).toEquiv
    _ = Nat.card (ZMod (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
        Nat.card_congr (RingEquiv.toEquiv (PadicInt.residueField (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ))))
    _ = Rat.HeightOneSpectrum.natGenerator v := Nat.card_zmod _

end MPP.Solutions.Bsd099
