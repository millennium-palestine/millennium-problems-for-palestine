import Mathlib
import MPP.Defs.BSD
import MPP.Solutions.Bsd035
import MPP.Solutions.Bsd043
import MPP.Solutions.Bsd044

namespace MPP.Solutions.Bsd038

open MPP.BSD

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ h : E.toAffine.Point → ℝ,
    (∀ P : E.toAffine.Point, 0 ≤ h P) ∧
    (∀ P : E.toAffine.Point, h (-P) = h P) ∧
    (∀ M : ℝ, {P : E.toAffine.Point | h P ≤ M}.Finite) ∧
    (∃ C : ℝ, ∀ P Q : E.toAffine.Point, h (P + Q) ≤ 2 * h P + 2 * h Q + C) ∧
    (∃ D : ℝ, ∀ P : E.toAffine.Point, 4 * h P - D ≤ h (2 • P)) := by
  intro E _
  obtain ⟨H, hH⟩ : ∃ H : E.toAffine.Point → ℝ, ∀ P : E.toAffine.Point, H P = match P with
      | WeierstrassCurve.Affine.Point.zero => 0
      | WeierstrassCurve.Affine.Point.some x _ _ =>
          Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ)) :=
    ⟨_, fun P => rfl⟩
  refine ⟨H, ?_, ?_, ?_, Bsd044.main E H hH, Bsd043.main E H hH⟩
  · intro P
    cases P with
    | zero => rw [hH]
    | some x y h =>
      rw [hH]
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ max (x.num.natAbs : ℝ) (x.den : ℝ) :=
        le_max_of_le_left (Nat.cast_nonneg _)
      linarith
  · intro P
    cases P with
    | zero =>
      show H (-(0 : E.toAffine.Point)) = H 0
      rw [neg_zero]
    | some x y h =>
      show H (-(WeierstrassCurve.Affine.Point.some x y h)) = H (WeierstrassCurve.Affine.Point.some x y h)
      rw [WeierstrassCurve.Affine.Point.neg_some, hH, hH]
  · intro M
    apply Set.Finite.subset (Bsd035.main E ⌈Real.exp M⌉₊)
    intro P hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      right
      have e : H (WeierstrassCurve.Affine.Point.some x y h)
          = Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ)) := by
        rw [hH]
      have hP' : Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ)) ≤ M := by
        rw [← e]
        exact hP
      have hnn : (0 : ℝ) ≤ max (x.num.natAbs : ℝ) (x.den : ℝ) :=
        le_max_of_le_left (Nat.cast_nonneg _)
      have hle : 1 + max (x.num.natAbs : ℝ) (x.den : ℝ) ≤ Real.exp M :=
        (Real.log_le_iff_le_exp (by linarith)).mp hP'
      have hceil : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
      have hm : max (x.num.natAbs : ℝ) (x.den : ℝ) ≤ (⌈Real.exp M⌉₊ : ℝ) := by linarith
      have h1 : (x.num.natAbs : ℝ) ≤ (⌈Real.exp M⌉₊ : ℝ) := (le_max_left _ _).trans hm
      have h2 : (x.den : ℝ) ≤ (⌈Real.exp M⌉₊ : ℝ) := (le_max_right _ _).trans hm
      refine ⟨x, y, h, rfl, ?_, ?_⟩
      · exact_mod_cast h1
      · exact_mod_cast h2

end MPP.Solutions.Bsd038
