import Mathlib

namespace MPP.Solutions.Bsd374

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (m : ℕ)
    (P : W.toAffine.Point), Odd m → m • P = 0 → 2 • P = 0 → P = 0 := by
  intro K _ _ W m P hodd hm h2
  obtain ⟨k, rfl⟩ := hodd
  calc P = (2 * k + 1) • P - k • (2 • P) := by module
    _ = 0 := by rw [hm, h2]; simp

end MPP.Solutions.Bsd374
