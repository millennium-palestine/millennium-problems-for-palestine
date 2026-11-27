import Mathlib
import MPP.Solutions.Bsd361

namespace MPP.Solutions.Bsd288

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    W.a₁ = 0 → W.a₂ = 0 → W.a₃ = 0 →
    ∃ A B : Polynomial K,
      A * W.preΨ' 5 + B * Polynomial.derivative (W.preΨ' 5) =
        Polynomial.C ((5 : K) ^ 12 * W.Δ ^ 22) := by
  intro K _ W h1 h2 h3
  have hf : (W.preΨ' 5).natDegree ≤ 12 := by
    rw [MPP.Solutions.Bsd361.preΨ5_formula K W h1 h2 h3]
    compute_degree!
  have hg : (Polynomial.derivative (W.preΨ' 5)).natDegree ≤ 11 := by
    have := Polynomial.natDegree_derivative_le (W.preΨ' 5)
    omega
  obtain ⟨p, q, -, -, h⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant (W.preΨ' 5) (Polynomial.derivative (W.preΨ' 5))
      hf hg (Or.inl (by norm_num))
  rw [MPP.Solutions.Bsd361.main K W h1 h2 h3] at h
  exact ⟨p, q, by linear_combination h⟩

end MPP.Solutions.Bsd288
