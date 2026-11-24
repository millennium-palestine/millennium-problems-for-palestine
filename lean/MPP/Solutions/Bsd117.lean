import Mathlib
import MPP.Solutions.Bsd085
import MPP.Solutions.Bsd112
import MPP.Solutions.Bsd114

namespace MPP.Solutions.Bsd117

theorem main : ∀ (p q e : ℚ) (g : Polynomial ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q → e ^ 3 + p * e + q = 0 →
    g = Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) → Irreducible g →
    ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y), y ≠ 0 →
      ∀ β : AdjoinRoot g, β ^ 2 = AdjoinRoot.of g x - AdjoinRoot.root g →
        ∃ R : E.toAffine.Point, R + R = WeierstrassCurve.Affine.Point.some x y h := by
  intro p q e g E _ ha1 ha2 ha3 ha4 ha6 hcub hgdef hirr x y h hy β hβ
  obtain ⟨u, v, h1, h2⟩ := MPP.Solutions.Bsd112.main p e g hgdef hirr x β
    (by rw [AdjoinRoot.algebraMap_eq]; exact hβ)
  have hN := MPP.Solutions.Bsd114.main p e u v x h1 h2
  have hcurve : y ^ 2 = (x - e) * (x ^ 2 + e * x + (e ^ 2 + p)) := by
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq + hcub
  have hNne : u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p) ≠ 0 := by
    intro hN0
    have hev : g.eval x = x ^ 2 + e * x + (e ^ 2 + p) := by
      rw [hgdef]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
    have hgx : g.eval x = 0 := by
      rw [hev, hN, hN0]
      norm_num
    have hdeg : g.degree = 2 := by
      rw [hgdef]
      compute_degree!
    have h1' := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := x) hgx
    rw [hdeg] at h1'
    exact absurd h1' (by decide)
  have hsq : x - e = (y / (u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p))) ^ 2 := by
    rw [div_pow, hcurve, hN, mul_div_assoc, div_self (pow_ne_zero 2 hNne), mul_one]
  exact MPP.Solutions.Bsd085.main p q e x y E ha1 ha2 ha3 ha4 ha6 hcub h hy
    ⟨y / (u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p)), u, v, hsq.symm, h1, h2⟩

end MPP.Solutions.Bsd117
