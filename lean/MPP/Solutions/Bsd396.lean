import Mathlib
import MPP.Solutions.Bsd221
import MPP.Solutions.Bsd271
import MPP.Solutions.Bsd395

namespace MPP.Solutions.Bsd396

-- the Ψ₂Sq value at an affine point is the square of 2y + a₁x + a₃
lemma psi2_eval {K : Type} [Field K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (-4) * hE

-- the triple x-coordinate formula (bsd-394), proved as in that solution
lemma triple {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y x₃ y₃ : K)
    (h : W.toAffine.Nonsingular x y) (h₃ : W.toAffine.Nonsingular x₃ y₃)
    (h3P : (3 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x₃ y₃ h₃) :
    x₃ * (W.Ψ₃.eval x) ^ 2 = x * (W.Ψ₃.eval x) ^ 2 - W.Ψ₂Sq.eval x * W.preΨ₄.eval x := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hD' : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hΨ : W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := psi2_eval W x y h
  have hP3 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
      ((WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ := by
    rw [← h3P, three_nsmul]
  by_cases hyne : y = W.toAffine.negY x y
  · have h2 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyne
    have hP : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ := by
      rw [← hP3, h2, add_zero]
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hP
    have hz : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have hD := hD'
      rw [← hyne, sub_self] at hD
      exact hD.symm
    rw [← hP.1, hΨ, hz]
    ring
  · have key := MPP.Solutions.Bsd271.main K W x y x₃ y₃ h h₃ hyne hP3
    norm_num [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq]
    linear_combination key

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    (7 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (W.preΨ' 7).eval x = 0 := by
  intro K _ _ W x y h h7
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h with hP
  have hP0 : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero h
  have h3ne : (3 : ℕ) • P ≠ 0 := by
    intro h3z
    have e : P = (7 : ℕ) • P - (2 : ℕ) • ((3 : ℕ) • P) := by abel
    rw [h7, h3z, nsmul_zero, sub_zero] at e
    exact hP0 e
  have h4ne : (4 : ℕ) • P ≠ 0 := by
    intro h4z
    apply h3ne
    have e : (3 : ℕ) • P = (7 : ℕ) • P - (4 : ℕ) • P := by abel
    rw [e, h7, h4z, sub_zero]
  -- y ≠ negY: otherwise 2 • P = 0 and P = 7 • P − 3 • (2 • P) = 0
  have hy : y ≠ W.toAffine.negY x y := by
    intro hyne
    have h2 : P + P = 0 := WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyne
    have e : P = (7 : ℕ) • P - (3 : ℕ) • (P + P) := by abel
    rw [h7, h2, nsmul_zero, sub_zero] at e
    exact hP0 e
  have hF : W.Ψ₂Sq.eval x ≠ 0 := by
    rw [psi2_eval W x y h]
    refine pow_ne_zero 2 (fun h0 => hy ?_)
    rw [WeierstrassCurve.Affine.negY]
    linear_combination h0
  -- 2 • P = (x₂, y₂) by bsd-221
  obtain ⟨x₂, y₂, h₂, hQ, hx₂⟩ := MPP.Solutions.Bsd221.main K W x y h hy
  have h2 : x₂ * W.Ψ₂Sq.eval x = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
    rw [psi2_eval W x y h]
    exact hx₂
  -- 4 • P = (x₄, y₄) by bsd-221 applied to 2 • P
  have hy2 : y₂ ≠ W.toAffine.negY x₂ y₂ := by
    intro hy2
    apply h4ne
    have hQQ : (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy2
    have e : (4 : ℕ) • P = (P + P) + (P + P) := by abel
    rw [e, hQ]
    exact hQQ
  obtain ⟨x₄, y₄, h₄, hQ4, hx₄⟩ := MPP.Solutions.Bsd221.main K W x₂ y₂ h₂ hy2
  have h4 : x₄ * W.Ψ₂Sq.eval x₂ = x₂ ^ 4 - W.b₄ * x₂ ^ 2 - 2 * W.b₆ * x₂ - W.b₈ := by
    rw [psi2_eval W x₂ y₂ h₂]
    exact hx₄
  have h4P : (4 : ℕ) • P = WeierstrassCurve.Affine.Point.some x₄ y₄ h₄ := by
    have e : (4 : ℕ) • P = (P + P) + (P + P) := by abel
    rw [e, hQ]
    exact hQ4
  -- 3 • P is affine: x₃ is its x-coordinate
  obtain ⟨x₃, y₃, h₃, h3P⟩ : ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (3 : ℕ) • P = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ := by
    cases hT : (3 : ℕ) • P with
    | zero => exact absurd hT h3ne
    | some x₃ y₃ h₃ => exact ⟨x₃, y₃, h₃, rfl⟩
  have h3 := triple W x y x₃ y₃ h h₃ h3P
  -- 4 • P = −(3 • P) because 7 • P = 0, so x₄ = x₃
  have hx34 : x₃ = x₄ := by
    have e7 : (4 : ℕ) • P + (3 : ℕ) • P = 0 := by
      have e : (4 : ℕ) • P + (3 : ℕ) • P = (7 : ℕ) • P := by abel
      rw [e, h7]
    have hneg : (4 : ℕ) • P = -((3 : ℕ) • P) := eq_neg_of_add_eq_zero_left e7
    rw [h4P, h3P, WeierstrassCurve.Affine.Point.neg_some] at hneg
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hneg
    exact hneg.1.symm
  exact MPP.Solutions.Bsd395.main K W x x₂ x₃ x₄ hF h2 h4 h3 hx34

end MPP.Solutions.Bsd396
