import Mathlib

namespace MPP.Solutions.Bsd282

theorem main : ∀ (K : Type) [Field K] (f u v : Polynomial K) (c : K), c ≠ 0 →
    u * f + v * Polynomial.derivative f = Polynomial.C c → Squarefree f := by
  intro K _ f u v c hc h
  apply Polynomial.Separable.squarefree
  refine ⟨Polynomial.C c⁻¹ * u, Polynomial.C c⁻¹ * v, ?_⟩
  calc Polynomial.C c⁻¹ * u * f + Polynomial.C c⁻¹ * v * Polynomial.derivative f
      = Polynomial.C c⁻¹ * (u * f + v * Polynomial.derivative f) := by ring
    _ = Polynomial.C c⁻¹ * Polynomial.C c := by rw [h]
    _ = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]

end MPP.Solutions.Bsd282
