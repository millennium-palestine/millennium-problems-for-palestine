import Mathlib
import MPP.Solutions.Bsd288
import MPP.Solutions.Bsd289

namespace MPP.Solutions.Bsd284

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    (2 : K) ≠ 0 → (3 : K) ≠ 0 → (5 : K) ≠ 0 →
    ∃ A B : Polynomial K,
      A * W.preΨ' 5 + B * Polynomial.derivative (W.preΨ' 5) =
        Polynomial.C ((5 : K) ^ 12 * W.Δ ^ 22) := by
  intro K _ W h2 h3 _
  obtain ⟨r, W', h1', h2', h3', hΔ, hf⟩ := MPP.Solutions.Bsd289.main K W h2 h3
  obtain ⟨A, B, hAB⟩ := MPP.Solutions.Bsd288.main K W' h1' h2' h3'
  rw [hΔ] at hAB
  refine ⟨A.comp (Polynomial.X - Polynomial.C r), B.comp (Polynomial.X - Polynomial.C r), ?_⟩
  have hd : Polynomial.derivative (Polynomial.X - Polynomial.C r : Polynomial K) = 1 := by
    simp
  have key := congrArg (fun p => Polynomial.comp p (Polynomial.X - Polynomial.C r)) hAB
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp] at key
  rw [hf, Polynomial.derivative_comp, hd, one_mul]
  linear_combination key

end MPP.Solutions.Bsd284
