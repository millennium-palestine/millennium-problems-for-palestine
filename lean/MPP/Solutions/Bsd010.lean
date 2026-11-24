import Mathlib

namespace MPP.Solutions.Bsd010

open WeierstrassCurve

/-- y² = x³ − x over `ZMod 3`. -/
abbrev E3 : WeierstrassCurve (ZMod 3) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

/-- The x-coordinate of an affine point, or `none` for the point at infinity. -/
def xOf : WeierstrassCurve.Affine.Point E3 → Option (ZMod 3)
  | .zero => none
  | .some x _ _ => some x

theorem hΔ : E3.Δ ≠ 0 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  decide

/-- Over `ZMod 3`, the equation y² = x³ − x forces y = 0. -/
theorem y_zero : ∀ x y : ZMod 3, y ^ 2 = x ^ 3 - x → y = 0 := by decide

theorem equation_zero : ∀ x : ZMod 3, E3.toAffine.Equation x 0 := by
  intro x
  rw [WeierstrassCurve.Affine.equation_iff]
  fin_cases x <;> decide

theorem point_eq : ∀ P Q : WeierstrassCurve.Affine.Point E3, xOf P = xOf Q → P = Q
  | .zero, .zero, _ => rfl
  | .zero, .some _ _ _, h => by simp [xOf] at h
  | .some _ _ _, .zero, h => by simp [xOf] at h
  | .some x y hP, .some x' y' hQ, h => by
      have hxx : x = x' := by simpa [xOf] using h
      subst hxx
      have hyE : y ^ 2 = x ^ 3 - x := by
        have h1 := hP.1
        rw [WeierstrassCurve.Affine.equation_iff] at h1
        linear_combination h1
      have hyE' : y' ^ 2 = x ^ 3 - x := by
        have h1 := hQ.1
        rw [WeierstrassCurve.Affine.equation_iff] at h1
        linear_combination h1
      have hy0 : y = 0 := y_zero x y hyE
      have hy0' : y' = 0 := y_zero x y' hyE'
      subst hy0 hy0'
      rfl

theorem main : Nat.card (WeierstrassCurve.Affine.Point E3) = 4 := by
  have hinj : Function.Injective xOf := fun P Q h => point_eq P Q h
  have hsurj : Function.Surjective xOf := by
    intro o
    cases o with
    | none => exact ⟨.zero, rfl⟩
    | some x =>
      have hns : E3.toAffine.Nonsingular x 0 :=
        (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (equation_zero x)
      exact ⟨WeierstrassCurve.Affine.Point.some x 0 hns, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective xOf ⟨hinj, hsurj⟩)]
  simp [Nat.card_eq_fintype_card]

end MPP.Solutions.Bsd010
