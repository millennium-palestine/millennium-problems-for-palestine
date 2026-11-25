import Mathlib

namespace MPP.Solutions.Bsd190

theorem exists_algebraMap_of_pow_eq (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p))
    (hx : x ^ p = x) : ∃ a : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a = x := by
  have hmem : x ∈ (⊥ : Subfield (AlgebraicClosure (ZMod p))) :=
    (Subfield.mem_bot_iff_pow_eq_self _ p).mpr hx
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p _).mp hmem
  exact ⟨(n : ZMod p), by rw [map_intCast, hn]⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))]
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    let φ := WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // P - φ P = 0} =
      Nat.card (W.baseChange (ZMod p)).toAffine.Point := by
  intro p _ _ W _
  dsimp only
  have hfix : ∀ Q : (W.baseChange (ZMod p)).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
        (WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p)
          (AlgebraicClosure (ZMod p)) Q) =
        WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p)
          (AlgebraicClosure (ZMod p)) Q :=
    fun Q => WeierstrassCurve.Affine.Point.map_baseChange
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) Q
  have hinj : Function.Injective
      (WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) (AlgebraicClosure (ZMod p))) :=
    WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
  have hbij : Function.Bijective (fun Q : (W.baseChange (ZMod p)).toAffine.Point =>
      (⟨WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) (AlgebraicClosure (ZMod p)) Q,
        sub_eq_zero.mpr (hfix Q).symm⟩ :
        {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
          P - WeierstrassCurve.Affine.Point.map (W' := W)
            (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = 0})) := by
    refine ⟨fun Q Q' h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨P, hP⟩
    have hPφ := sub_eq_zero.mp hP
    cases P with
    | zero => exact ⟨0, Subtype.ext rfl⟩
    | some x y h =>
      simp only [WeierstrassCurve.Affine.Point.map_some] at hPφ
      obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hPφ
      have hxp : x ^ p = x := by
        simpa [FiniteField.frobeniusAlgHom_apply, ZMod.card] using hx.symm
      have hyp : y ^ p = y := by
        simpa [FiniteField.frobeniusAlgHom_apply, ZMod.card] using hy.symm
      obtain ⟨a, rfl⟩ := exists_algebraMap_of_pow_eq p x hxp
      obtain ⟨b, rfl⟩ := exists_algebraMap_of_pow_eq p y hyp
      have hn : (W.baseChange (ZMod p)).toAffine.Nonsingular a b :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
          (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))).injective a b).mp h
      exact ⟨WeierstrassCurve.Affine.Point.some _ _ hn, Subtype.ext rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

end MPP.Solutions.Bsd190
