import Mathlib
import MPP.Solutions.Bsd264
import MPP.Solutions.Bsd265

namespace MPP.Solutions.Bsd256

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (x y : K)
    (h : W.toAffine.Nonsingular x y),
    (7 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (W.preΨ' 7).eval x = 0 := by
  intro K _ _ W _ x y h h7
  -- a point killed by 7 and by 3, 2 or 4 is zero
  have z3 : ∀ Q : W.toAffine.Point, (7 : ℤ) • Q = 0 → (3 : ℤ) • Q = 0 → Q = 0 := by
    intro Q hQ7 hQ3
    have e : Q = (7 : ℤ) • Q - (2 : ℤ) • ((3 : ℤ) • Q) := by
      rw [← mul_zsmul]
      abel
    rw [e, hQ7, hQ3]
    simp
  have z2 : ∀ Q : W.toAffine.Point, (7 : ℤ) • Q = 0 → (2 : ℤ) • Q = 0 → Q = 0 := by
    intro Q hQ7 hQ2
    have e : Q = (7 : ℤ) • Q - (3 : ℤ) • ((2 : ℤ) • Q) := by
      rw [← mul_zsmul]
      abel
    rw [e, hQ7, hQ2]
    simp
  have z4 : ∀ Q : W.toAffine.Point, (7 : ℤ) • Q = 0 → (4 : ℤ) • Q = 0 → Q = 0 := by
    intro Q hQ7 hQ4
    have e : Q = (2 : ℤ) • ((4 : ℤ) • Q) - (7 : ℤ) • Q := by
      rw [← mul_zsmul]
      abel
    rw [e, hQ7, hQ4]
    simp
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hP : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero h
  -- 2P is affine: 2y + a₁x + a₃ ≠ 0, since 2P = 0 would give P = 0
  have hD : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hD0
    have hyeq : y = W.toAffine.negY x y := by
      rw [WeierstrassCurve.Affine.negY]
      linear_combination hD0
    apply hP
    apply z2 _ h7
    have h2 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyeq
    have e : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) := by
      abel
    rw [e, h2]
  -- 3P and 4P are nonzero, hence affine
  have h3ne : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 :=
    fun h0 => hP (z3 _ h7 h0)
  have h4ne : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 :=
    fun h0 => hP (z4 _ h7 h0)
  have key : ∀ Q : W.toAffine.Point, Q ≠ 0 → ∃ (a b : K) (hab : W.toAffine.Nonsingular a b),
      Q = WeierstrassCurve.Affine.Point.some a b hab := by
    intro Q hQ
    cases Q with
    | zero => exact absurd rfl hQ
    | @some a b hab => exact ⟨a, b, hab, rfl⟩
  obtain ⟨x3, y3, h3, hQ3⟩ := key _ h3ne
  obtain ⟨x4, y4, h4, hQ4⟩ := key _ h4ne
  -- 3P = -(4P) because 7P = 0, so the x-coordinates agree
  have hsum : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
      (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
    rw [← add_zsmul, show (3 : ℤ) + 4 = 7 by norm_num]
    exact h7
  rw [hQ3, hQ4] at hsum
  have hxeq : x3 = x4 :=
    WeierstrassCurve.Affine.Point.X_eq_iff.mpr (Or.inr (eq_neg_of_add_eq_zero_left hsum))
  -- the chord relations for 3P (bsd-264) and 4P (bsd-265)
  have hA := MPP.Solutions.Bsd264.main K W x y x3 y3 h h3 hD hQ3
  have hB := MPP.Solutions.Bsd265.main K W x y x4 y4 h h4 hD hQ4
  rw [← hxeq] at hB
  -- the seven-division polynomial, from Mathlib's recursion
  have h5 : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    have h := W.preΨ'_odd 0
    norm_num at h
    linear_combination h
  have h7eq : W.preΨ' 7 = (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 - W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
    have h := W.preΨ'_odd 1
    norm_num at h
    rw [h5] at h
    linear_combination h
  rw [h7eq]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
  simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq]
  linear_combination (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 2 * hB -
    (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) *
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
        (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2 * hA

end MPP.Solutions.Bsd256
