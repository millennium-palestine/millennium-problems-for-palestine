import Mathlib
import MPP.Solutions.Bsd296

namespace MPP.Solutions.Bsd299

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic],
    (3 : K) = 0 → (5 : K) ≠ 0 → W.a₁ = 0 → W.a₃ = 0 → W.a₂ ≠ 0 → Squarefree (W.preΨ' 5) := by
  intro K _ W _ h3 h5 ha1 ha3 _
  exact MPP.Solutions.Bsd296.main K W h3 h5 ha1 ha3

end MPP.Solutions.Bsd299
