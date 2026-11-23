import Mathlib
import MPP.Defs.BSD

namespace MPP.Solutions.Bsd001

open MPP.BSD

theorem main : E32.Δ = 64 := by
  unfold E32 WeierstrassCurve.Δ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    WeierstrassCurve.b₆ WeierstrassCurve.b₈
  norm_num

end MPP.Solutions.Bsd001
