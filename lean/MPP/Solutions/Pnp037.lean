import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp037

open MPP.PvsNP Turing

theorem main : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)) :=
  ⟨idComputableInPolyTime (id : List Bool → List Bool)⟩

end MPP.Solutions.Pnp037
