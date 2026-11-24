import Mathlib
import MPP.Solutions.Bsd060

namespace MPP.Solutions.Bsd107

theorem main : ∀ (e1 e2 e3 : ℤ), e1 + e2 + e3 = 0 → e1 ≠ e2 → e1 ≠ e3 → e2 ≠ e3 →
    ∃ D : Finset ℤ, ∀ (x y : ℚ), y ^ 2 = (x - e1) * (x - e2) * (x - e3) →
      (x ≠ e1 → ∃ d ∈ D, ∃ u : ℚ, x - e1 = (d : ℚ) * u ^ 2) ∧
      (x ≠ e2 → ∃ d ∈ D, ∃ u : ℚ, x - e2 = (d : ℚ) * u ^ 2) ∧
      (x ≠ e3 → ∃ d ∈ D, ∃ u : ℚ, x - e3 = (d : ℚ) * u ^ 2) := by
  intro e1 e2 e3 hs h12 h13 h23
  obtain ⟨D1, hD1⟩ := MPP.Solutions.Bsd060.main e1 e2 e3 hs h12 h13 h23
  obtain ⟨D2, hD2⟩ := MPP.Solutions.Bsd060.main e2 e1 e3 (by linarith) (Ne.symm h12) h23 h13
  obtain ⟨D3, hD3⟩ := MPP.Solutions.Bsd060.main e3 e1 e2 (by linarith) (Ne.symm h13) (Ne.symm h23) h12
  refine ⟨D1 ∪ D2 ∪ D3, fun x y hxy => ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨d, hd, u, hu⟩ := hD1 x y hxy hx
    exact ⟨d, by simp [hd], u, hu⟩
  · obtain ⟨d, hd, u, hu⟩ := hD2 x y (by rw [hxy]; ring) hx
    exact ⟨d, by simp [hd], u, hu⟩
  · obtain ⟨d, hd, u, hu⟩ := hD3 x y (by rw [hxy]; ring) hx
    exact ⟨d, by simp [hd], u, hu⟩

end MPP.Solutions.Bsd107
