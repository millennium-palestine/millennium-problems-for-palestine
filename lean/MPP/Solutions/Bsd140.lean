import Mathlib

namespace MPP.Solutions.Bsd140

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

theorem iter_fixed_iff (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))]
    (W : WeierstrassCurve (ZMod p)) (n : ℕ) (x y : AlgebraicClosure (ZMod p))
    (h : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Nonsingular x y) :
    ((fun P => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P)^[n]
      (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x y h) ↔
      (x ^ (p ^ n) = x ∧ y ^ (p ^ n) = y) := by
  obtain ⟨h', he⟩ := iter_some p W n x y h
  rw [he]
  constructor
  · intro hs
    obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj hs
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact some_congr _ _ _ _ _ _ _ h1 h2

-- every element of the algebraic closure of F_p is fixed by some positive power of the p-power map
theorem exists_pow_eq_self (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p)) :
    ∃ m : ℕ, 0 < m ∧ x ^ (p ^ m) = x := by
  set F := IntermediateField.adjoin (ZMod p) ({x} : Set (AlgebraicClosure (ZMod p))) with hF
  haveI : FiniteDimensional (ZMod p) F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : Finite F := Module.finite_of_finite (ZMod p)
  haveI : Fintype F := Fintype.ofFinite F
  have hpos : 0 < Module.finrank (ZMod p) F := Module.finrank_pos
  have hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  refine ⟨Module.finrank (ZMod p) F, hpos, ?_⟩
  let y : F := ⟨x, IntermediateField.mem_adjoin_simple_self _ _⟩
  have hy : y ^ (p ^ Module.finrank (ZMod p) F) = y := by
    rw [← hcard]
    exact FiniteField.pow_card y
  have := congrArg Subtype.val hy
  simpa [y] using this

-- powers of a fixed exponent are fixed as well
theorem pow_fix (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p)) (m : ℕ)
    (hx : x ^ (p ^ m) = x) (j : ℕ) :
    x ^ (p ^ (m * j)) = x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show m * (j + 1) = m * j + m by ring, pow_add, mul_comm (p ^ (m * j)) (p ^ m), pow_mul, hx, ih]

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p))
    (P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    ∃ n : ℕ, 0 < n ∧ (fun Q => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) Q)^[n] P = P := by
  intro p _ _ W P
  cases P with
  | zero => exact ⟨1, one_pos, by rw [Function.iterate_one]; exact WeierstrassCurve.Affine.Point.map_zero _⟩
  | some x y h =>
    obtain ⟨m, hm, hx⟩ := exists_pow_eq_self p x
    obtain ⟨k, hk, hy⟩ := exists_pow_eq_self p y
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    rw [iter_fixed_iff]
    refine ⟨pow_fix p x m hx k, ?_⟩
    rw [mul_comm m k]
    exact pow_fix p y k hy m

end MPP.Solutions.Bsd140
