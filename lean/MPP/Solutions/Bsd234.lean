import Mathlib
import MPP.Solutions.Bsd232
import MPP.Solutions.Bsd233

namespace MPP.Solutions.Bsd234

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K)
    [W.IsElliptic], (2 : K) ≠ 0 → 4 ≤ Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0} := by
  intro K _ _ _ W _ h2
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 * 2 * 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have hΔ : W.Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ W).ne_zero
  have hdisc : W.b₂ ^ 2 * (2 * W.b₄) ^ 2 - 4 * 4 * (2 * W.b₄) ^ 3 - 4 * W.b₂ ^ 3 * W.b₆ -
      27 * 4 ^ 2 * W.b₆ ^ 2 + 18 * 4 * W.b₂ * (2 * W.b₄) * W.b₆ ≠ 0 := by
    rw [MPP.Solutions.Bsd232.main K W]
    exact mul_ne_zero h16 hΔ
  have hcube := MPP.Solutions.Bsd233.main K 4 W.b₂ (2 * W.b₄) W.b₆ h4 hdisc
  -- a point killed by 2 has y determined by x: 2y + a₁x + a₃ = 0
  have hL231 : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      2 * y + W.a₁ * x + W.a₃ = 0 := by
    intro x y h hP
    rw [two_nsmul] at hP
    have h' := eq_neg_of_add_eq_zero_left hP
    rw [WeierstrassCurve.Affine.Point.neg_some] at h'
    have hy := (WeierstrassCurve.Affine.Point.some.inj h').right
    change y = -y - W.a₁ * x - W.a₃ at hy
    linear_combination hy
  -- the x-coordinate of an affine 2-torsion point is a root of the 2-division cubic
  have hxroot : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    intro x y h hP
    have hLx := hL231 x y h hP
    have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
      (WeierstrassCurve.Affine.equation_iff x y).mp h.left
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (2 * y + W.a₁ * x + W.a₃) * hLx - 4 * hE
  -- the y-coordinate attached to a root of the cubic
  let ycoord : K → K := fun x => -(W.a₁ * x + W.a₃) * 2⁻¹
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hyL : ∀ x : K, 2 * ycoord x + W.a₁ * x + W.a₃ = 0 := by
    intro x
    simp only [ycoord]
    linear_combination (-(W.a₁ * x + W.a₃)) * hinv
  have hEq : ∀ x : K, 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 →
      W.toAffine.Equation x (ycoord x) := by
    intro x hx
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hx
    have h4E : (4 : K) * ((ycoord x) ^ 2 + W.a₁ * x * ycoord x + W.a₃ * ycoord x -
        (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
      linear_combination (2 * ycoord x + W.a₁ * x + W.a₃) * hyL x - hx
    have hE := (mul_eq_zero.mp h4E).resolve_left h4
    linear_combination hE
  have hns : ∀ x : K, 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 →
      W.toAffine.Nonsingular x (ycoord x) := fun x hx =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp (hEq x hx)
  -- the roots of the cubic are finitely many, since there are at least three of them
  have hfinR : Finite {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0} :=
    Nat.finite_of_card_ne_zero (by omega)
  -- the affine 2-torsion point attached to a root
  let G : {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0} → W.toAffine.Point :=
    fun x => WeierstrassCurve.Affine.Point.some x.1 (ycoord x.1) (hns x.1 x.2)
  have hGtors : ∀ x : {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0},
      (2 : ℕ) • G x = 0 := by
    intro x
    show (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x.1 (ycoord x.1) (hns x.1 x.2)) = 0
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by
      show ycoord x.1 = -(ycoord x.1) - W.a₁ * x.1 - W.a₃
      linear_combination hyL x.1)
  -- the 2-torsion is finite: it is {0} together with the points G x
  have hfinS : Set.Finite {P : W.toAffine.Point | (2 : ℕ) • P = 0} := by
    refine Set.Finite.subset ((Set.finite_range G).insert 0) ?_
    intro P hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      right
      have hLy := hL231 x y h hP
      have hX := hxroot x y h hP
      refine ⟨⟨x, hX⟩, ?_⟩
      have h2y : (2 : K) * (y - ycoord x) = 0 := by linear_combination hLy - hyL x
      have hyy : y = ycoord x := sub_eq_zero.mp ((mul_eq_zero.mp h2y).resolve_left h2)
      show WeierstrassCurve.Affine.Point.some x (ycoord x) (hns x hX) =
        WeierstrassCurve.Affine.Point.some x y h
      subst hyy
      rfl
  haveI : Finite {P : W.toAffine.Point // (2 : ℕ) • P = 0} := hfinS.to_subtype
  -- {0} and the points G x: an injection from Option of the roots
  have hinj : Function.Injective (fun o : Option {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0} =>
      (Option.elim o ⟨0, smul_zero _⟩ (fun x => ⟨G x, hGtors x⟩) :
        {P : W.toAffine.Point // (2 : ℕ) • P = 0})) := by
    intro o1 o2 h
    cases o1 with
    | none =>
      cases o2 with
      | none => rfl
      | some x =>
        exact absurd (congrArg Subtype.val h).symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
    | some x =>
      cases o2 with
      | none =>
        exact absurd (congrArg Subtype.val h) (WeierstrassCurve.Affine.Point.some_ne_zero _)
      | some x' =>
        have hG : WeierstrassCurve.Affine.Point.some x.1 (ycoord x.1) (hns x.1 x.2) =
            WeierstrassCurve.Affine.Point.some x'.1 (ycoord x'.1) (hns x'.1 x'.2) :=
          congrArg Subtype.val h
        exact congrArg some (Subtype.ext (WeierstrassCurve.Affine.Point.some.inj hG).1)
  have hcount := Nat.card_le_card_of_injective _ hinj
  have hO : Nat.card (Option {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0}) =
      Nat.card {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0} + 1 := by
    haveI := Fintype.ofFinite {x : K // 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0}
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Nat.card_eq_fintype_card]
  omega

end MPP.Solutions.Bsd234
