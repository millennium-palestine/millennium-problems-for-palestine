import Mathlib
import MPP.Solutions.Bsd040
import MPP.Solutions.Bsd041

namespace MPP.Solutions.Bsd042

theorem main : ∀ S : Finset ℕ, ∃ D : Finset ℤ, ∀ q : ℚ, q ≠ 0 →
    (∀ p : ℕ, p.Prime → ((p : ℤ) ∣ q.num ∨ p ∣ q.den) → p ∈ S) →
      ∃ d ∈ D, ∃ u : ℚ, q = (d : ℚ) * u ^ 2 := by
  intro S
  refine ⟨(MPP.Solutions.Bsd040.main S).toFinset, ?_⟩
  intro q hq hS
  obtain ⟨d, u, hsq, hqd, hsupp⟩ := MPP.Solutions.Bsd041.main q hq
  refine ⟨d, ?_, u, hqd⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨hsq, fun p hp hpd => hS p hp (hsupp p hp hpd)⟩

end MPP.Solutions.Bsd042
