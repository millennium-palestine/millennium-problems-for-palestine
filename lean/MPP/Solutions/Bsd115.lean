import Mathlib
import MPP.Solutions.Bsd100
import MPP.Solutions.Bsd108

namespace MPP.Solutions.Bsd115

theorem main : ∀ (p e : ℚ) (g : Polynomial ℚ), g = Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) →
    Irreducible g → ∃ D : Finset (AdjoinRoot g), ∀ x y : ℚ, y ^ 2 = (x - e) * (x ^ 2 + e * x + (e ^ 2 + p)) →
      ∃ d ∈ D, ∃ u : AdjoinRoot g, algebraMap ℚ (AdjoinRoot g) x - AdjoinRoot.root g = d * u ^ 2 := by
  intro p e g hg hirr
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hdeg : g.degree = 2 := by
    rw [hg]
    compute_degree!
  have hθne : ∀ x : ℚ, algebraMap ℚ (AdjoinRoot g) x ≠ AdjoinRoot.root g := by
    intro x hx
    have hg0 : Polynomial.aeval (AdjoinRoot.root g) g = 0 := by
      rw [Polynomial.aeval_def]
      exact AdjoinRoot.eval₂_root g
    rw [← hx, Polynomial.aeval_algebraMap_apply] at hg0
    have hgx : g.eval x = 0 := (map_eq_zero_iff (algebraMap ℚ (AdjoinRoot g)) (algebraMap ℚ (AdjoinRoot g)).injective).mp hg0
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := x) hgx
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  obtain ⟨S, hS, hpar⟩ := MPP.Solutions.Bsd108.main p e g hg
  obtain ⟨D, hD⟩ := MPP.Solutions.Bsd100.main (AdjoinRoot g) S hS
  refine ⟨D, ?_⟩
  intro x y hxy
  obtain ⟨d, hd, u, hu⟩ := hD (algebraMap ℚ (AdjoinRoot g) x - AdjoinRoot.root g)
    (sub_ne_zero.mpr (hθne x)) (fun v hv => hpar x y hxy v hv)
  exact ⟨d, hd, u, hu⟩

end MPP.Solutions.Bsd115
