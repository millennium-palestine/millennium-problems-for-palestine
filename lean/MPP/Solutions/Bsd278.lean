import Mathlib
import MPP.Solutions.Bsd293
import MPP.Solutions.Bsd294

namespace MPP.Solutions.Bsd278

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    (5 : K) ≠ 0 → Squarefree (W.preΨ' 5) := by
  intro K _ _ W hW h5
  by_cases h23 : (2 : K) = 0 ∨ (3 : K) = 0
  · exact MPP.Solutions.Bsd294.main K W h23 h5
  · push_neg at h23
    exact MPP.Solutions.Bsd293.main K W h23.1 h23.2 h5

end MPP.Solutions.Bsd278
