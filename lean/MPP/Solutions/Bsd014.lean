import Mathlib
import MPP.Defs.BSD
import MPP.Solutions.Bsd011
import MPP.Solutions.Bsd012
import MPP.Solutions.Bsd013

namespace MPP.Solutions.Bsd014

open MPP.BSD WeierstrassCurve

theorem hΔ : E32.toAffine.Δ ≠ 0 := by
  show E32.Δ ≠ 0
  simp [E32, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- A point of E32 at height `x` with `x³ − x = 0` and `y = 0` is nonsingular. -/
theorem ns_zero (x : ℚ) (hx : x ^ 3 - x = 0) : E32.toAffine.Nonsingular x 0 := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E32]
  linear_combination -hx

/-- Every affine point of E32 has y = 0 and x ∈ {0, 1, −1}. -/
theorem affine_pt (x y : ℚ) (h : E32.toAffine.Nonsingular x y) :
    y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  have hcurve : y ^ 2 = x ^ 3 - x := by
    have h1 := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at h1
    simp only [E32] at h1
    linear_combination h1
  have hy : y = 0 := by
    by_contra hy0
    obtain ⟨a, b, c, ha, hb, hc, heq⟩ := MPP.Solutions.Bsd011.main x y hcurve hy0
    exact MPP.Solutions.Bsd012.main a b c ha hb hc heq
  subst hy
  exact ⟨rfl, MPP.Solutions.Bsd013.main x 0 hcurve rfl⟩

theorem main : Finite E32.toAffine.Point := by
  let p0 : E32.toAffine.Point := .some 0 0 (ns_zero 0 (by norm_num))
  let p1 : E32.toAffine.Point := .some 1 0 (ns_zero 1 (by norm_num))
  let pm1 : E32.toAffine.Point := .some (-1) 0 (ns_zero (-1) (by norm_num))
  let F : Fin 4 → E32.toAffine.Point := ![0, p0, p1, pm1]
  have hsurj : Function.Surjective F := by
    intro P
    cases P with
    | zero => exact ⟨0, rfl⟩
    | @some x y h =>
      obtain ⟨hy, hx⟩ := affine_pt x y h
      subst hy
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  exact Finite.of_surjective F hsurj

end MPP.Solutions.Bsd014
