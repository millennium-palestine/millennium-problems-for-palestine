import Mathlib
import MPP.Defs.BSD
import MPP.Solutions.Bsd011
import MPP.Solutions.Bsd012
import MPP.Solutions.Bsd013

namespace MPP.Solutions.Bsd005

open MPP.BSD WeierstrassCurve

theorem disc_ne_zero : E32.toAffine.Δ ≠ 0 := by
  show E32.Δ ≠ 0
  simp [E32, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem nonsing_of_equation (x y : ℚ) (h : E32.toAffine.Equation x y) :
    E32.toAffine.Nonsingular x y :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero disc_ne_zero).mp h

theorem curve_eq (x y : ℚ) (h : E32.toAffine.Nonsingular x y) : y ^ 2 = x ^ 3 - x := by
  have h1 := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at h1
  simp [E32] at h1
  linear_combination h1

theorem ns00 : E32.toAffine.Nonsingular 0 0 :=
  nonsing_of_equation 0 0 (by simp [WeierstrassCurve.Affine.equation_iff, E32])

theorem ns10 : E32.toAffine.Nonsingular 1 0 :=
  nonsing_of_equation 1 0 (by norm_num [WeierstrassCurve.Affine.equation_iff, E32])

theorem nsm10 : E32.toAffine.Nonsingular (-1) 0 :=
  nonsing_of_equation (-1) 0 (by norm_num [WeierstrassCurve.Affine.equation_iff, E32])

theorem classify (P : E32.toAffine.Point) :
    P = 0 ∨ P = WeierstrassCurve.Affine.Point.some 0 0 ns00 ∨
      P = WeierstrassCurve.Affine.Point.some 1 0 ns10 ∨
      P = WeierstrassCurve.Affine.Point.some (-1) 0 nsm10 := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    have hcurve : y ^ 2 = x ^ 3 - x := curve_eq x y h
    by_cases hy : y = 0
    · subst hy
      rcases MPP.Solutions.Bsd013.main x 0 hcurve rfl with hx | hx | hx
      · subst hx
        exact Or.inr (Or.inl rfl)
      · subst hx
        exact Or.inr (Or.inr (Or.inl rfl))
      · subst hx
        exact Or.inr (Or.inr (Or.inr rfl))
    · exfalso
      obtain ⟨a, b, c, ha, hb, hc, hE⟩ := MPP.Solutions.Bsd011.main x y hcurve hy
      exact (MPP.Solutions.Bsd012.main a b c ha hb hc hE).elim

theorem finite_points : Finite E32.toAffine.Point := by
  have hsub : (Set.univ : Set E32.toAffine.Point) ⊆
      ({0, WeierstrassCurve.Affine.Point.some 0 0 ns00,
        WeierstrassCurve.Affine.Point.some 1 0 ns10,
        WeierstrassCurve.Affine.Point.some (-1) 0 nsm10} : Set E32.toAffine.Point) := by
    intro P _
    rcases classify P with h | h | h | h <;> simp [h]
  exact Set.finite_univ_iff.mp (Set.Finite.subset (Set.toFinite _) hsub)

theorem main : Module.rank ℤ E32.toAffine.Point = 0 := by
  haveI := finite_points
  rw [rank_eq_zero_iff_isTorsion]
  intro x
  obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).mp (isOfFinAddOrder_of_finite x)
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
  show (n : ℤ) • x = 0
  rw [natCast_zsmul]
  exact hnx

end MPP.Solutions.Bsd005
