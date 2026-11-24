import Mathlib

namespace MPP.Solutions.Bsd143

open Finset

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    [(WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).IsElliptic], p ≠ 2 →
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)) ^ 2 ≤ 4 * (p : ℤ) →
    |((Nat.card (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤
      2 * Real.sqrt (p : ℝ) := by
  -- the point count identity, proved inline (it is bsd-141)
  have h141 : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p)
      [(WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).IsElliptic], p ≠ 2 →
      ((Nat.card (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Point : ℕ) : ℤ) =
        (p : ℤ) + 1 + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
    intro p _ a b _ hp
    have hchar : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp
    have hEq : ∀ xy : ZMod p × ZMod p,
        (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Nonsingular xy.1 xy.2 ↔
          xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1 + b := by
      intro xy
      rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
      simp
    have key : ∀ x : ZMod p,
        ((univ.filter (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card : ℤ) =
          quadraticChar (ZMod p) (x ^ 3 + a * x + b) + 1 := by
      intro x
      have h := quadraticChar_card_sqrts hchar (x ^ 3 + a * x + b)
      simpa [Set.toFinset_setOf] using h
    have hS : ((Nat.card {xy : ZMod p × ZMod p //
        (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Nonsingular xy.1 xy.2} : ℕ) : ℤ) =
        ∑ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 + a * x + b) + 1) := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight hEq), Nat.card_eq_fintype_card,
        Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← key x, Finset.card_filter]
      push_cast
      rfl
    rw [Nat.card_congr (WeierstrassCurve.Affine.nonsingularPointEquiv
      (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine)]
    change ((Nat.card (Option {xy : ZMod p × ZMod p //
      (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Nonsingular xy.1 xy.2}) : ℕ) : ℤ) = _
    rw [Finite.card_option, Nat.cast_add, Nat.cast_one, hS, Finset.sum_add_distrib]
    simp [ZMod.card]
    ring
  intro p _ a b _ hp hS
  have hD := h141 p a b hp
  have hD' : ((Nat.card (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1) =
      ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) : ℤ) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hD
    push_cast at h ⊢
    linarith
  rw [hD']
  have hS' : (((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) : ℤ) : ℝ)) ^ 2 ≤ 4 * (p : ℝ) := by
    exact_mod_cast hS
  have h4 : Real.sqrt (4 * (p : ℝ)) = 2 * Real.sqrt (p : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hS'

end MPP.Solutions.Bsd143
