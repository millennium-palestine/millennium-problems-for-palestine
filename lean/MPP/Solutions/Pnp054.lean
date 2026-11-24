import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp022
import MPP.Solutions.Pnp050
import MPP.Solutions.Pnp053

namespace MPP.Solutions.Pnp054

open MPP.PvsNP Turing

/-- A polynomial with natural coefficients is monotone on `ℕ`. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range a, Polynomial.eval_eq_sum_range b]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- The doubled first component of the pair encoding has twice the length of the instance. -/
theorem pair_length_ge (x u : List Bool) : x.length ≤ (pair x u).length := by
  have hd : ∀ y : List Bool, (y.flatMap fun b => [b, b]).length = 2 * y.length := by
    intro y
    induction y with
    | nil => rfl
    | cons a y ih => simp [List.flatMap_cons, ih]; omega
  simp only [pair, List.length_append, hd, List.length_cons, List.length_nil]
  omega

/-- Search-to-decision step: the prefix-extension language of a polynomial-time verifier is in NP. -/
theorem main : ∀ V : Lang, InP V → ∀ p : Polynomial ℕ, ∃ D : Lang, InNP D ∧
    ∀ x u : List Bool, D (pair x u) = true ↔
      ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x (u ++ w)) = true := by
  intro V hV p
  classical
  -- decoder d of pnp-021, its transport s of pnp-022, the exact-length test E of pnp-050,
  -- and the flattening r of pnp-053
  obtain ⟨d, ⟨Td⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨s, ⟨Ts⟩, hs_eq⟩ := MPP.Solutions.Pnp022.main d ⟨Td⟩
  obtain ⟨E, hE, hE_eq⟩ := MPP.Solutions.Pnp050.main p
  obtain ⟨r, ⟨Tr⟩, hr_eq⟩ := MPP.Solutions.Pnp053.main
  -- W y = E (s y) && V (r y) is in P
  have hEs : InP (fun x => E (s x)) := MPP.Solutions.Pnp008.main E s hE Ts
  have hVr : InP (fun x => V (r x)) := MPP.Solutions.Pnp008.main V r hV Tr
  have hW0 : InP (fun x => E (s x) && V (r x)) := MPP.Solutions.Pnp011.main _ _ hEs hVr
  obtain ⟨W, hW_eq⟩ : ∃ W : Lang, ∀ y, W y = (E (s y) && V (r y)) :=
    ⟨fun y => E (s y) && V (r y), fun _ => rfl⟩
  have hW : InP W := by
    have hfun : W = fun x => E (s x) && V (r x) := funext hW_eq
    rw [hfun]
    exact hW0
  have hWpair : ∀ x u w : List Bool,
      W (pair (pair x u) w) = (E (pair x w) && V (pair x (u ++ w))) := by
    intro x u w
    rw [hW_eq, hs_eq, hd_eq, hr_eq]
  -- D z holds when some witness w with |w| ≤ p(|z|) makes W accept the pair z w
  refine ⟨fun z => decide (∃ w : List Bool, w.length ≤ p.eval z.length ∧ W (pair z w) = true),
    ⟨W, hW, p, fun z => ?_⟩, fun x u => ?_⟩
  · simp only [decide_eq_true_iff]
  · simp only [decide_eq_true_iff, hWpair, Bool.and_eq_true, hE_eq]
    constructor
    · rintro ⟨w, -, hw, hV'⟩
      exact ⟨w, hw, hV'⟩
    · rintro ⟨w, hw, hV'⟩
      refine ⟨w, ?_, hw, hV'⟩
      rw [hw]
      exact eval_mono p (pair_length_ge x u)

end MPP.Solutions.Pnp054
