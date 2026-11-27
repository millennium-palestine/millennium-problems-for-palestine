import Mathlib
import MPP.Solutions.Bsd354
import MPP.Solutions.Bsd355

namespace MPP.Solutions.Bsd356

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K), (4 : K) ≠ 0 →
    Nat.card {P : W.toAffine.Point // (4 : ℕ) • P = 0} ≤ 16 := by
  intro K _ _ W h4
  have h := MPP.Solutions.Bsd354.main K W 4 ⟨2, rfl⟩ (by exact_mod_cast h4)
    (fun x y hxy h1 h2 => MPP.Solutions.Bsd355.main K W x y hxy h1 h2)
  norm_num at h
  exact h

end MPP.Solutions.Bsd356
