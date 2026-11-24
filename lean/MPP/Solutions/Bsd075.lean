import Mathlib
import MPP.Solutions.Bsd100
import MPP.Solutions.Bsd101

namespace MPP.Solutions.Bsd075

theorem main : ∀ (p q : ℚ) (f : Polynomial ℚ),
    f = Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q →
    Irreducible f → ∃ D : Finset (AdjoinRoot f), ∀ x y : ℚ, y ^ 2 = x ^ 3 + p * x + q →
      ∃ d ∈ D, ∃ u : AdjoinRoot f, algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f = d * u ^ 2 := by
  intro p q f hf hirr
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hdeg : f.degree = 3 := by
    rw [hf]
    compute_degree!
  have hθne : ∀ x : ℚ, algebraMap ℚ (AdjoinRoot f) x ≠ AdjoinRoot.root f := by
    intro x hx
    have hf0 : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      rw [Polynomial.aeval_def]
      exact AdjoinRoot.eval₂_root f
    rw [← hx, Polynomial.aeval_algebraMap_apply] at hf0
    have hfx : f.eval x = 0 := by
      have := (map_eq_zero_iff (algebraMap ℚ (AdjoinRoot f)) (algebraMap ℚ (AdjoinRoot f)).injective).mp hf0
      exact this
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := x) hfx
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  obtain ⟨S, hS, hpar⟩ := MPP.Solutions.Bsd101.main p q f hf
  obtain ⟨D, hD⟩ := MPP.Solutions.Bsd100.main (AdjoinRoot f) S hS
  refine ⟨D, ?_⟩
  intro x y hxy
  have hne := hθne x
  obtain ⟨d, hd, u, hu⟩ := hD (algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f)
    (sub_ne_zero.mpr hne) (fun v hv => hpar x y hxy hne v hv)
  exact ⟨d, hd, u, hu⟩

end MPP.Solutions.Bsd075
