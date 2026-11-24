import Mathlib
import MPP.Solutions.Bsd103
import MPP.Solutions.Bsd118
import MPP.Solutions.Bsd127
import MPP.Solutions.Bsd128

namespace MPP.Solutions.Bsd129

theorem main : ∀ (p q : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
    E.a₄ = p → E.a₆ = q →
    ∃ s : Finset E.toAffine.Point, ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro p q E _ ha1 ha2 ha3 ha4 ha6
  classical
  by_cases hirr : Irreducible (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ)
  · exact MPP.Solutions.Bsd103.main p q E ha1 ha2 ha3 ha4 ha6 hirr
  -- the cubic is reducible, so it has a rational root e
  have hf3 : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ).natDegree = 3 := by
    compute_degree!
  have hf0 : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ) ≠ 0 := by
    intro h0
    rw [h0] at hf3
    simp at hf3
  obtain ⟨e, he⟩ : ∃ e : ℚ, e ^ 3 + p * e + q = 0 := by
    have hne : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ).roots ≠ 0 := by
      intro h0
      exact hirr ((Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr h0)
    obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hne
    refine ⟨e, ?_⟩
    have := (Polynomial.mem_roots hf0).mp he
    simpa [Polynomial.IsRoot.def] using this
  -- the factorization (X − e)·g with g = X² + eX + (e² + p)
  have hfac : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ) =
      (Polynomial.X - Polynomial.C e) *
        (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p)) := by
    have hC : Polynomial.C (e ^ 3 + p * e + q) = 0 := by rw [he, map_zero]
    simp only [map_add, map_mul, map_pow] at hC
    simp only [map_add, map_pow]
    linear_combination hC
  by_cases hgirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) :
      Polynomial ℚ)
  · exact MPP.Solutions.Bsd118.main p q e _ E ha1 ha2 ha3 ha4 ha6 he rfl hgirr
  -- the quadratic factor is reducible, so it has a rational root e2, and the roots are e, e2, −e − e2
  have hg0 : (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) : Polynomial ℚ) ≠ 0 := by
    intro h0
    have hgdeg : (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) :
        Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    rw [h0] at hgdeg
    simp at hgdeg
  obtain ⟨e2, he2⟩ : ∃ e2 : ℚ, e2 ^ 2 + e * e2 + (e ^ 2 + p) = 0 := by
    have hgdeg : (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) :
        Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    have hne : (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) :
        Polynomial ℚ).roots ≠ 0 := by
      intro h0
      exact hgirr ((Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr h0)
    obtain ⟨e2, he2⟩ := Multiset.exists_mem_of_ne_zero hne
    refine ⟨e2, ?_⟩
    have := (Polynomial.mem_roots hg0).mp he2
    simpa [Polynomial.IsRoot.def] using this
  have hs : e + e2 + (-e - e2) = 0 := by ring
  have hp' : p = e * e2 + e * (-e - e2) + e2 * (-e - e2) := by linear_combination he2
  have hq' : q = -(e * e2 * (-e - e2)) := by linear_combination he - e * he2
  obtain ⟨h12, h13, h23⟩ := MPP.Solutions.Bsd127.main p q e e2 (-e - e2) E ha1 ha2 ha3 ha4 ha6 hs hp' hq'
  exact MPP.Solutions.Bsd128.main p q e e2 (-e - e2) E ha1 ha2 ha3 ha4 ha6 hs hp' hq' h12 h13 h23

end MPP.Solutions.Bsd129
