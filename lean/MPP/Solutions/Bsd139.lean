import Mathlib

namespace MPP.Solutions.Bsd139

open WeierstrassCurve Polynomial

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

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p))
    (n : ℕ), 0 < n →
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      (fun P => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P)^[n] P = P} ≤ (p ^ n) ^ 2 + 1 := by
  intro p _ _ W n hn
  classical
  have hq : 1 < p ^ n := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  have hne : (X ^ (p ^ n) - X : (AlgebraicClosure (ZMod p))[X]) ≠ 0 := by
    intro h
    have := FiniteField.X_pow_card_sub_X_natDegree_eq (AlgebraicClosure (ZMod p)) hq
    rw [h, natDegree_zero] at this
    omega
  -- the roots of X^(p^n) - X, i.e. the coordinates fixed by the p^n-power map
  set S : Finset (AlgebraicClosure (ZMod p)) := (X ^ (p ^ n) - X : (AlgebraicClosure (ZMod p))[X]).roots.toFinset
    with hSdef
  have hS : ∀ x : AlgebraicClosure (ZMod p), x ∈ S ↔ x ^ (p ^ n) = x := by
    intro x
    rw [hSdef, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
  have hSc : S.card ≤ p ^ n := by
    calc S.card ≤ (X ^ (p ^ n) - X : (AlgebraicClosure (ZMod p))[X]).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (X ^ (p ^ n) - X : (AlgebraicClosure (ZMod p))[X]).natDegree := card_roots' _
      _ = p ^ n := FiniteField.X_pow_card_sub_X_natDegree_eq (AlgebraicClosure (ZMod p)) hq
  -- the target finset: the point at infinity and the pairs of fixed coordinates
  set U : Finset (Option (AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))) :=
    insert none ((S ×ˢ S).map ⟨some, Option.some_injective _⟩) with hUdef
  have hU : U.card ≤ (p ^ n) ^ 2 + 1 := by
    calc U.card ≤ ((S ×ˢ S).map ⟨some, Option.some_injective _⟩).card + 1 := Finset.card_insert_le _ _
      _ = S.card * S.card + 1 := by rw [Finset.card_map, Finset.card_product]
      _ ≤ (p ^ n) ^ 2 + 1 := Nat.add_le_add_right (by rw [sq]; exact Nat.mul_le_mul hSc hSc) 1
  -- the map to options of coordinates
  let G : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point →
      Option (AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p)) := fun P =>
    match P with
    | .zero => none
    | .some (x := x) (y := y) _ => some (x, y)
  have hmem : ∀ P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point,
      ((fun P => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P)^[n] P = P) → G P ∈ U := by
    intro P hP
    cases P with
    | zero => exact Finset.mem_insert_self _ _
    | some x y h =>
      obtain ⟨hx, hy⟩ := (iter_fixed_iff p W n x y h).mp hP
      refine Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨(x, y), Finset.mem_product.mpr
        ⟨(hS x).mpr hx, (hS y).mpr hy⟩, rfl⟩)
  have hinj : Function.Injective (fun P : {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      (fun P => WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P)^[n] P = P} =>
      (⟨G P.1, hmem P.1 P.2⟩ : {o // o ∈ U})) := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
    have hGPQ : G P = G Q := congrArg Subtype.val hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x y h => simp [G] at hGPQ
    | some x y h =>
      cases Q with
      | zero => simp [G] at hGPQ
      | some x' y' h' =>
        simp only [G, Option.some.injEq, Prod.mk.injEq] at hGPQ
        obtain ⟨rfl, rfl⟩ := hGPQ
        rfl
  have hle := Nat.card_le_card_of_injective _ hinj
  have hcard : Nat.card {o // o ∈ U} = U.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard] at hle
  exact hle.trans hU

end MPP.Solutions.Bsd139
