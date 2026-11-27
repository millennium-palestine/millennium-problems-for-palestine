import Mathlib
import MPP.Solutions.Bsd367

namespace MPP.Solutions.Bsd402

theorem main : ∀ (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p)), x ^ p = x →
    ∃ a : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a = x :=
  MPP.Solutions.Bsd367.main

end MPP.Solutions.Bsd402
