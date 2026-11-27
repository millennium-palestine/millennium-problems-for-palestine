import Mathlib

namespace MPP.Solutions.Bsd345

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (m : ℤ),
    W.ψ (m + 0) * W.ψ (m - 0) =
      W.ψ (m + 1) * W.ψ (m - 1) * W.ψ 0 ^ 2 - W.ψ (0 + 1) * W.ψ (0 - 1) * W.ψ m ^ 2 ∧
    W.ψ (m + 1) * W.ψ (m - 1) =
      W.ψ (m + 1) * W.ψ (m - 1) * W.ψ 1 ^ 2 - W.ψ (1 + 1) * W.ψ (1 - 1) * W.ψ m ^ 2 := by
  intro K _ W m
  refine ⟨?_, ?_⟩
  · simp [WeierstrassCurve.ψ_zero, WeierstrassCurve.ψ_one, WeierstrassCurve.ψ_neg]
    ring
  · norm_num [WeierstrassCurve.ψ_zero, WeierstrassCurve.ψ_one]

end MPP.Solutions.Bsd345
