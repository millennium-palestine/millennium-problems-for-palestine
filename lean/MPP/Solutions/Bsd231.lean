import Mathlib

namespace MPP.Solutions.Bsd231

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    (2 : K) ≠ 0 → Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0} ≤ 4 := by
  intro K _ _ W _ h2
  -- a point killed by 2 is either zero or satisfies 2y + a₁x + a₃ = 0
  have hL : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      2 * y + W.a₁ * x + W.a₃ = 0 := by
    intro x y h hP
    rw [two_nsmul] at hP
    have h' := eq_neg_of_add_eq_zero_left hP
    rw [WeierstrassCurve.Affine.Point.neg_some] at h'
    have hy := (WeierstrassCurve.Affine.Point.some.inj h').right
    change y = -y - W.a₁ * x - W.a₃ at hy
    linear_combination hy
  -- the 2-division cubic 4x³ + b₂x² + 2b₄x + b₆
  obtain ⟨F, hF⟩ : ∃ F : Polynomial K, F = Polynomial.C 4 * Polynomial.X ^ 3 +
      Polynomial.C W.b₂ * Polynomial.X ^ 2 + Polynomial.C (2 * W.b₄) * Polynomial.X +
      Polynomial.C W.b₆ := ⟨_, rfl⟩
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hF0 : F ≠ 0 := by
    intro h0
    rw [hF] at h0
    have hc := congrArg (fun p => Polynomial.coeff p 3) h0
    simp at hc
    exact h4 hc
  have hdeg : F.natDegree ≤ 3 := by
    rw [hF]
    exact Polynomial.natDegree_cubic_le
  have hZcard : F.roots.toFinset.card ≤ 3 :=
    le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' F) hdeg)
  -- the x-coordinate of a nonzero 2-torsion point is a root of the cubic
  have hxroot : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      x ∈ F.roots.toFinset := by
    intro x y h hP
    have hLx := hL x y h hP
    have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
      (WeierstrassCurve.Affine.equation_iff x y).mp h.left
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hF0, Polynomial.IsRoot.def, hF]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination (2 * y + W.a₁ * x + W.a₃) * hLx - 4 * hE
  -- the target finset: the point at infinity and the x-coordinates
  let T : Finset (Option K) := insert none (F.roots.toFinset.map Function.Embedding.some)
  have hT : T.card ≤ 4 :=
    le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_map]; omega)
  let f : W.toAffine.Point → Option K := fun P => match P with
    | .zero => none
    | .some x _ _ => some x
  have hmem : ∀ P : {P : W.toAffine.Point // (2 : ℕ) • P = 0}, f P.1 ∈ T := by
    rintro ⟨P, hP⟩
    cases P with
    | zero => exact Finset.mem_insert_self _ _
    | some x y h =>
      exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ (hxroot x y h hP))
  have hinj : Function.Injective
      (fun P : {P : W.toAffine.Point // (2 : ℕ) • P = 0} => (⟨f P.1, hmem P⟩ : T)) := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
    have hfPQ : f P = f Q := congrArg Subtype.val hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x y h => exact absurd hfPQ (by simp [f])
    | some x y h =>
      cases Q with
      | zero => exact absurd hfPQ (by simp [f])
      | some x' y' h' =>
        have hxx : x = x' := Option.some.inj hfPQ
        subst hxx
        have hy1 := hL x y h hP
        have hy2 := hL x y' h' hQ
        have hyy : y = y' := by
          have h2y : (2 : K) * (y - y') = 0 := by linear_combination hy1 - hy2
          have := (mul_eq_zero.mp h2y).resolve_left h2
          linear_combination this
        subst hyy
        rfl
  calc Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0}
      ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 4 := hT

end MPP.Solutions.Bsd231
