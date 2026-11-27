import Mathlib
import MPP.Solutions.Bsd354
import MPP.Solutions.Bsd359

namespace MPP.Solutions.Bsd360

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K), (8 : K) ≠ 0 →
    Nat.card {P : W.toAffine.Point // (8 : ℕ) • P = 0} ≤ 64 := by
  intro K _ _ W h8
  have h := MPP.Solutions.Bsd354.main K W 8 ⟨4, rfl⟩ (by exact_mod_cast h8)
    (fun x y hxy h1 h2 => MPP.Solutions.Bsd359.main K W x y hxy h1 h2)
  norm_num at h
  exact h

end MPP.Solutions.Bsd360
