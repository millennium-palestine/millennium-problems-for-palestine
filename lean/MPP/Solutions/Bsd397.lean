import Mathlib
import MPP.Solutions.Bsd316
import MPP.Solutions.Bsd396

namespace MPP.Solutions.Bsd397

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K), (7 : K) ≠ 0 →
    Nat.card {P : W.toAffine.Point // (7 : ℕ) • P = 0} ≤ 49 := by
  intro K _ _ W h7
  have h := MPP.Solutions.Bsd316.main K W 7 ⟨3, rfl⟩ (by exact_mod_cast h7)
    (fun x y hxy h1 => MPP.Solutions.Bsd396.main K W x y hxy h1)
  norm_num at h
  exact h

end MPP.Solutions.Bsd397
