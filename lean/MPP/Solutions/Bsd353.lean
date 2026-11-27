import Mathlib

namespace MPP.Solutions.Bsd353

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K), (2 : K) ≠ 0 →
    Nat.card {P : W.toAffine.Point // 2 • P = 0} ≤ 4 := by
  intro K _ _ W h2
  -- an affine point with 2 • P = 0 has 2y + a₁x + a₃ = 0
  have key : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      2 * y + W.a₁ * x + W.a₃ = 0 := by
    intro x y h hP
    rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some] at hP
    have hy := (WeierstrassCurve.Affine.Point.some.inj hP).2
    simp only [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  -- the x-coordinate of such a point is a root of the cubic 4x³ + b₂x² + 2b₄x + b₆
  have cubic : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    intro x y h hP
    have hD := key x y h hP
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp
      ((WeierstrassCurve.Affine.nonsingular_iff x y).mp h).1
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (2 * y + W.a₁ * x + W.a₃) * hD - 4 * heq
  obtain ⟨p, hpdef⟩ : ∃ p : Polynomial K, p = Polynomial.C 4 * Polynomial.X ^ 3
      + Polynomial.C W.b₂ * Polynomial.X ^ 2 + Polynomial.C (2 * W.b₄) * Polynomial.X
      + Polynomial.C W.b₆ := ⟨_, rfl⟩
  have h4 : (4 : K) ≠ 0 := by
    have h := mul_ne_zero h2 h2
    norm_num at h
    exact h
  have hdeg : p.natDegree = 3 := by
    rw [hpdef]
    exact Polynomial.natDegree_cubic h4
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    norm_num at hdeg
  have hroots : p.roots.toFinset.card ≤ 3 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans hdeg.le)
  have hroot : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      x ∈ p.roots.toFinset := by
    intro x y h hP
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hpdef]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact cubic x y h hP
  -- the target: none for the zero point, some x for an affine point
  obtain ⟨F, hFdef⟩ : ∃ F : Finset (Option K),
      F = insert none (p.roots.toFinset.map ⟨Option.some, Option.some_injective K⟩) := ⟨_, rfl⟩
  have hF : F.card ≤ 4 := by
    have h1 := Finset.card_insert_le none (p.roots.toFinset.map ⟨Option.some, Option.some_injective K⟩)
    rw [Finset.card_map] at h1
    rw [hFdef]
    omega
  let g : W.toAffine.Point → Option K := fun P => match P with
    | .zero => none
    | .some x _ _ => some x
  have hmem : ∀ P : {P : W.toAffine.Point // 2 • P = 0}, g P.1 ∈ F := by
    rintro ⟨P, hP⟩
    rw [hFdef]
    cases P with
    | zero => exact Finset.mem_insert_self _ _
    | some x y h =>
      exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨x, hroot x y h hP, rfl⟩)
  have hinj : Function.Injective (fun P : {P : W.toAffine.Point // 2 • P = 0} =>
      (⟨g P.1, hmem P⟩ : {z // z ∈ F})) := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
    have hPQ' : g P = g Q := congrArg Subtype.val hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x y h => simp [g] at hPQ'
    | some x y h =>
      cases Q with
      | zero => simp [g] at hPQ'
      | some x' y' h' =>
        have hx : x = x' := Option.some.inj hPQ'
        subst hx
        have hD := key x y h hP
        have hD' := key x y' h' hQ
        have hy : y = y' := by
          have h2y : (2 : K) * (y - y') = 0 := by linear_combination hD - hD'
          rcases mul_eq_zero.mp h2y with h0 | h0
          · exact absurd h0 h2
          · exact sub_eq_zero.mp h0
        subst hy
        rfl
  have hc := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := F), Fintype.card_coe] at hc
  omega

end MPP.Solutions.Bsd353
