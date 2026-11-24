import Mathlib

namespace MPP.Solutions.Bsd138

open WeierstrassCurve

theorem some_congr {K : Type*} [Field K] (W : WeierstrassCurve K) (a b a' b' : K)
    (hab : W.toAffine.Nonsingular a b) (hab' : W.toAffine.Nonsingular a' b')
    (ha : a = a') (hb : b = b') :
    WeierstrassCurve.Affine.Point.some a b hab = WeierstrassCurve.Affine.Point.some a' b' hab' := by
  subst ha
  subst hb
  rfl

theorem some_transport {K : Type*} [Field K] (W : WeierstrassCurve K) (a b a' b' : K)
    (hab : W.toAffine.Nonsingular a b) (ha : a = a') (hb : b = b') :
    ∃ h' : W.toAffine.Nonsingular a' b',
      WeierstrassCurve.Affine.Point.some a b hab = WeierstrassCurve.Affine.Point.some a' b' h' := by
  subst ha
  subst hb
  exact ⟨hab, rfl⟩

theorem frob_pow (p : ℕ) [Fact p.Prime] (a : AlgebraicClosure (ZMod p)) (n : ℕ) :
    FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) (a ^ (p ^ n)) = a ^ (p ^ (n + 1)) := by
  simp [ZMod.card, pow_succ, pow_mul]

theorem iter_some (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))]
    (W : WeierstrassCurve (ZMod p)) (n : ℕ) (x y : AlgebraicClosure (ZMod p))
    (h : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Nonsingular (x ^ (p ^ n)) (y ^ (p ^ n)),
      (fun P => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P)^[n]
        (WeierstrassCurve.Affine.Point.some x y h) =
        WeierstrassCurve.Affine.Point.some (x ^ (p ^ n)) (y ^ (p ^ n)) h' := by
  induction n with
  | zero =>
    obtain ⟨h', he⟩ := some_transport (W.baseChange (AlgebraicClosure (ZMod p))) x y
      (x ^ (p ^ 0)) (y ^ (p ^ 0)) h (by simp) (by simp)
    exact ⟨h', by rw [Function.iterate_zero, id, he]⟩
  | succ n ih =>
    obtain ⟨hh, he⟩ := ih
    rw [Function.iterate_succ_apply', he]
    rw [WeierstrassCurve.Affine.Point.map_some]
    exact some_transport _ _ _ _ _ _ (frob_pow p x n) (frob_pow p y n)

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) (n : ℕ)
    (x y : AlgebraicClosure (ZMod p)) (h : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Nonsingular x y),
    ((fun P => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P)^[n]
      (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x y h) ↔
      (x ^ (p ^ n) = x ∧ y ^ (p ^ n) = y) := by
  intro p _ _ W n x y h
  obtain ⟨h', he⟩ := iter_some p W n x y h
  rw [he]
  constructor
  · intro hs
    obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj hs
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact some_congr _ _ _ _ _ _ _ h1 h2

end MPP.Solutions.Bsd138
