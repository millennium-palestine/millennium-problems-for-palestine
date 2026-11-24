import Mathlib
import MPP.Solutions.Bsd141

namespace MPP.Solutions.Bsd152

open Finset

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    [(WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).IsElliptic], p ≠ 2 →
    (2 : ℤ) ∣ ((Nat.card (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Point : ℕ) : ℤ) -
      (1 + ((univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)) := by
  intro p _ a b _ hp
  have hcount := MPP.Solutions.Bsd141.main p a b hp
  -- parity of the character sum against p minus the number of roots (bsd-151, inlined)
  have hpar : (2 : ℤ) ∣ (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)) -
      ((p : ℤ) - ((univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)) := by
    have key : ∀ y : ZMod p,
        (2 : ℤ) ∣ quadraticChar (ZMod p) y - (if y = 0 then 0 else 1) := by
      intro y
      by_cases hy : y = 0
      · subst hy
        simp
      · rcases quadraticChar_dichotomy hy with h | h <;> simp [hy, h]
    have hle : (univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card ≤ p := by
      simpa [ZMod.card] using card_le_univ (univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0)
    have hsum : (p : ℤ) - ((univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)
        = ∑ x : ZMod p, (if x ^ 3 + a * x + b = 0 then (0 : ℤ) else 1) := by
      rw [Finset.sum_ite]
      simp [Finset.filter_not, Finset.card_univ_sdiff, ZMod.card, Nat.cast_sub hle]
    rw [hsum, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun x _ => key _
  obtain ⟨k, hk⟩ := hpar
  rw [hcount]
  exact ⟨k + (p : ℤ) - ((univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ), by linarith⟩

end MPP.Solutions.Bsd152
