import Mathlib
import MPP.Solutions.Bsd354
import MPP.Solutions.Bsd357

namespace MPP.Solutions.Bsd358

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K), (6 : K) ≠ 0 →
    Nat.card {P : W.toAffine.Point // (6 : ℕ) • P = 0} ≤ 36 := by
  intro K _ _ W h6
  have h := MPP.Solutions.Bsd354.main K W 6 ⟨3, rfl⟩ (by exact_mod_cast h6)
    (fun x y hxy h1 h2 => MPP.Solutions.Bsd357.main K W x y hxy h1 h2)
  norm_num at h
  exact h

end MPP.Solutions.Bsd358
