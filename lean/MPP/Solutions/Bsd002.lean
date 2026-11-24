import Mathlib
import MPP.Defs.BSD
import MPP.Solutions.Bsd036
import MPP.Solutions.Bsd111

namespace MPP.Solutions.Bsd002

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], AddGroup.FG E.toAffine.Point :=
  MPP.Solutions.Bsd111.main MPP.Solutions.Bsd036.main

end MPP.Solutions.Bsd002
