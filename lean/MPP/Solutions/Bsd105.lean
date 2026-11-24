import Mathlib
import MPP.Solutions.Bsd099

namespace MPP.Solutions.Bsd105

theorem card_points_map {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (W : WeierstrassCurve A) :
    Nat.card W.toAffine.Point = Nat.card (W.map e.toRingHom).toAffine.Point := by
  classical
  have key : ∀ xy : A × A, W.toAffine.Nonsingular xy.1 xy.2 ↔
      (W.map e.toRingHom).toAffine.Nonsingular (e xy.1) (e xy.2) := by
    intro xy
    exact (WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine) (f := e.toRingHom) e.injective
      xy.1 xy.2).symm
  let eq : {xy : A × A // W.toAffine.Nonsingular xy.1 xy.2} ≃
      {xy : B × B // (W.map e.toRingHom).toAffine.Nonsingular xy.1 xy.2} :=
    (Equiv.prodCongr e.toEquiv e.toEquiv).subtypeEquiv (fun xy => key xy)
  exact Nat.card_congr (W.toAffine.nonsingularPointEquiv.trans
    ((Equiv.optionCongr eq).trans (W.map e.toRingHom).toAffine.nonsingularPointEquiv.symm))

theorem main : (∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
      |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) →
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (a q : ℤ),
      ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
          (v.adicCompletionIntegers ℚ) →
        (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
          1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 →
        a ^ 2 ≤ 4 * q := by
  intro H E _ v a q hg hpoly
  have hp : (Rat.HeightOneSpectrum.natGenerator v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨hp⟩
  -- the good-reduction shape of the local polynomial, with explicit coefficients
  have hform : (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - Polynomial.C ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℤ) + 1 -
        (Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
          (v.adicCompletionIntegers ℚ)).toAffine.Point : ℤ)) * Polynomial.X +
        Polynomial.C ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℕ) : ℤ) *
          Polynomial.X ^ 2 := by
    rw [WeierstrassCurve.localPolynomial]
    simp only [hg, if_true]
  -- compare coefficients: q is the residue cardinality, a is q + 1 - #reduction
  have hpoly' := hpoly.symm.trans hform
  have hc1 := congrArg (fun f => Polynomial.coeff f 1) hpoly'
  have hc2 := congrArg (fun f => Polynomial.coeff f 2) hpoly'
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow] at hc1 hc2
  norm_num at hc1 hc2
  -- the residue field has p = natGenerator v elements
  have hcard := MPP.Solutions.Bsd099.main v
  -- the residue field is ZMod p
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let e0 :=Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    (R := NumberField.RingOfIntegers ℚ) v
  let e : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (Rat.HeightOneSpectrum.natGenerator v) :=
    (IsLocalRing.ResidueField.mapEquiv e0.toRingEquiv).trans
      (PadicInt.residueField (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)))
  -- the reduction over the residue field, transported to ZMod p
  haveI hell : ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
      (v.adicCompletionIntegers ℚ) |>.IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction (v.adicCompletionIntegers ℚ)).mp hg
  have hH := H (Rat.HeightOneSpectrum.natGenerator v)
    ((((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
      (v.adicCompletionIntegers ℚ)).map e.toRingHom)
  rw [← card_points_map e] at hH
  -- the two coefficient identities
  have hq : q = (Rat.HeightOneSpectrum.natGenerator v : ℤ) := by
    rw [← hcard]
    linarith
  have ha : a = ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℕ) : ℤ) + 1 -
      (Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
        (v.adicCompletionIntegers ℚ)).toAffine.Point : ℤ) := by
    linarith
  have hAR : (a : ℝ) = ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℝ) + 1 -
      ((Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
        (v.adicCompletionIntegers ℚ)).toAffine.Point : ℕ) : ℝ) := by
    rw [ha, hcard]
    push_cast
    ring
  have hbound : |(a : ℝ)| ≤ 2 * Real.sqrt ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℝ) := by
    rw [hAR, ← abs_neg]
    convert hH using 2
    ring
  have hsq : (a : ℝ) ^ 2 ≤ 4 * ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℝ) := by
    nlinarith [abs_nonneg (a : ℝ), Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (Rat.HeightOneSpectrum.natGenerator v)),
      sq_abs (a : ℝ), Real.sqrt_nonneg ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℝ)]
  have hint : a ^ 2 ≤ 4 * (Rat.HeightOneSpectrum.natGenerator v : ℤ) := by
    exact_mod_cast hsq
  rw [hq]
  exact hint

end MPP.Solutions.Bsd105
