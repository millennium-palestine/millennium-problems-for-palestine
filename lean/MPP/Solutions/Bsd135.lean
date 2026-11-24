import Mathlib
import MPP.Solutions.Bsd122

namespace MPP.Solutions.Bsd135

-- a point fixed by the Frobenius has coordinates in the prime field, so it is the image of an F_p-point
theorem mem_range_of_fixed (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))]
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point)
    (hP : WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P) :
    ∃ Q : (W.baseChange (ZMod p)).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := W)
        (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) Q = P := by
  cases P with
  | zero => exact ⟨0, WeierstrassCurve.Affine.Point.map_zero _⟩
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.map_some] at hP
    obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj hP
    have h1' : x ^ p = x := by simpa [ZMod.card] using h1
    have h2' : y ^ p = y := by simpa [ZMod.card] using h2
    obtain ⟨a, rfl⟩ := (MPP.Solutions.Bsd122.fixed_iff_prime p x).mp h1'
    obtain ⟨b, rfl⟩ := (MPP.Solutions.Bsd122.fixed_iff_prime p y).mp h2'
    have hn : (W.baseChange (ZMod p)).toAffine.Nonsingular a b :=
      (WeierstrassCurve.Affine.baseChange_nonsingular W
        (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))).toRingHom.injective a b).mp h
    exact ⟨WeierstrassCurve.Affine.Point.some a b hn, WeierstrassCurve.Affine.Point.map_some _ hn⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    let φ := WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
    φ P = P → φ (φ P) - (((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) • φ P) + (p : ℤ) • P = 0 := by
  intro p _ _ W _ P φ hP
  -- the base change of W from ZMod p to itself is W
  have hWid : W.baseChange (ZMod p) = W := by
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_id]
  have hN : Nat.card (W.baseChange (ZMod p)).toAffine.Point = Nat.card W.toAffine.Point := by
    rw [hWid]
  -- N • P = 0, where N = #E(F_p) and P is an F_p-point
  have hkey : Nat.card W.toAffine.Point • P = 0 := by
    obtain ⟨Q, rfl⟩ := mem_range_of_fixed p W P hP
    rw [← map_nsmul]
    have hQ : Nat.card W.toAffine.Point • Q = 0 := by
      rw [← hN]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard Q)
    rw [hQ, map_zero]
  have hz : (Nat.card W.toAffine.Point : ℤ) • P = 0 := by
    rw [natCast_zsmul]
    exact hkey
  have hφP : φ (φ P) = P := by
    simp only [hP]
  rw [hφP, hP, sub_smul, add_smul, one_smul, hz]
  abel

end MPP.Solutions.Bsd135
