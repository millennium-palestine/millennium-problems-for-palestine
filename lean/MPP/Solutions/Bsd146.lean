import Mathlib
import MPP.Solutions.Bsd143
import MPP.Solutions.Bsd144

namespace MPP.Solutions.Bsd146

open Finset

set_option maxRecDepth 10000

lemma small2 : ∀ (a₁ a₂ a₃ a₄ a₆ : ZMod 2), (WeierstrassCurve.mk a₁ a₂ a₃ a₄ a₆).Δ ≠ 0 →
    (((univ.filter (fun xy : ZMod 2 × ZMod 2 =>
      xy.2 ^ 2 + a₁ * xy.1 * xy.2 + a₃ * xy.2 = xy.1 ^ 3 + a₂ * xy.1 ^ 2 + a₄ * xy.1 + a₆)).card : ℤ)
      - 2) ^ 2 ≤ 8 := by
  decide

lemma small3 : ∀ (a₁ a₂ a₃ a₄ a₆ : ZMod 3), (WeierstrassCurve.mk a₁ a₂ a₃ a₄ a₆).Δ ≠ 0 →
    (((univ.filter (fun xy : ZMod 3 × ZMod 3 =>
      xy.2 ^ 2 + a₁ * xy.1 * xy.2 + a₃ * xy.2 = xy.1 ^ 3 + a₂ * xy.1 ^ 2 + a₄ * xy.1 + a₆)).card : ℤ)
      - 3) ^ 2 ≤ 12 := by
  decide

lemma hasse_small : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic], (p = 2 ∨ p = 3) →
    |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro p _ W _ hp
  have hEq : ∀ xy : ZMod p × ZMod p, W.toAffine.Nonsingular xy.1 xy.2 ↔
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆ := by
    intro xy
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have hcount : ((Nat.card W.toAffine.Point : ℕ) : ℤ) =
      1 + ((univ.filter (fun xy : ZMod p × ZMod p =>
        xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
          xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card : ℤ) := by
    rw [Nat.card_congr (WeierstrassCurve.Affine.nonsingularPointEquiv W.toAffine)]
    change ((Nat.card (Option {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2}) : ℕ) : ℤ) = _
    rw [Finite.card_option, Nat.card_congr (Equiv.subtypeEquivRight hEq), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    push_cast
    ring
  have hZ : (((Nat.card W.toAffine.Point : ℕ) : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) := by
    have hΔ : W.Δ ≠ 0 := isUnit_iff_ne_zero.mp W.isUnit_Δ
    rcases hp with rfl | rfl
    · rw [hcount]
      have := small2 W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ hΔ
      push_cast
      nlinarith [this]
    · rw [hcount]
      have := small3 W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ hΔ
      push_cast
      nlinarith [this]
  have hR : |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ Real.sqrt (4 * (p : ℝ)) := by
    apply Real.abs_le_sqrt
    have h'' : ((((Nat.card W.toAffine.Point : ℕ) : ℤ) - ((p : ℤ) + 1) : ℤ) : ℝ) ^ 2 ≤
        ((4 * (p : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hZ
    push_cast at h''
    exact h''
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4] at hR
  exact hR

theorem main : (∀ (q : ℕ) [Fact q.Prime] (a b : ZMod q) [(WeierstrassCurve.mk (0 : ZMod q) 0 0 a b).IsElliptic],
    q ≠ 2 → (∑ x : ZMod q, quadraticChar (ZMod q) (x ^ 3 + a * x + b)) ^ 2 ≤ 4 * (q : ℤ)) →
    ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro H p _ W _
  by_cases hp : p = 2 ∨ p = 3
  · exact hasse_small p W hp
  · have hp' : p ≠ 2 ∧ p ≠ 3 := not_or.mp hp
    obtain ⟨a, b, hE, hcount⟩ := MPP.Solutions.Bsd144.main p W hp'.1 hp'.2
    haveI := hE
    have h := MPP.Solutions.Bsd143.main p a b hp'.1 (H p a b hp'.1)
    rw [hcount]
    exact h

end MPP.Solutions.Bsd146
