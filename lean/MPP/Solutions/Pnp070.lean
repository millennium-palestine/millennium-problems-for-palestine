import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp050
import MPP.Solutions.Pnp052

namespace MPP.Solutions.Pnp070

open MPP.PvsNP Turing

/-- Evaluation of a polynomial with natural coefficients is monotone on `ℕ`. -/
theorem eval_mono (p : Polynomial ℕ) : Monotone (fun n : ℕ => p.eval n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a b hab
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add (hp hab) (hq hab)
  | monomial n c =>
    intro a b hab
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab n)

/-- Doubling each bit does not shorten a string. -/
theorem length_le_double (l : List Bool) : l.length ≤ (l.flatMap fun b => [b, b]).length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The first component of the pair encoding is at most the whole encoding. -/
theorem length_le_pair (x u : List Bool) : x.length ≤ (pair x u).length := by
  have := length_le_double x
  unfold pair
  simp only [List.length_append] at this ⊢
  omega

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V → PEqualsNP →
    ∃ D : Lang, InP D ∧
      ∀ x u : List Bool, D (pair x u) = true ↔
        ∃ t : List Bool, (u ++ t).length = p.eval x.length ∧ V (pair x (u ++ t)) = true := by
  intro V p hV hPNP
  classical
  obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨C, ⟨hC⟩, hCx⟩ := MPP.Solutions.Pnp052.main
  obtain ⟨E, hE, hEx⟩ := MPP.Solutions.Pnp050.main p
  obtain ⟨hed⟩ := MPP.Solutions.Pnp006.main hd he
  obtain ⟨hdd⟩ := MPP.Solutions.Pnp006.main hd hd
  obtain ⟨h1, ⟨hh1⟩, h1eq⟩ := MPP.Solutions.Pnp026.main (e ∘ d) e ⟨hed⟩ ⟨he⟩
  obtain ⟨hc1⟩ := MPP.Solutions.Pnp006.main hh1 hC
  obtain ⟨h2, ⟨hh2⟩, h2eq⟩ := MPP.Solutions.Pnp026.main (d ∘ d) (C ∘ h1) ⟨hdd⟩ ⟨hc1⟩
  -- on `pair (pair x u) w`, the map `h2` returns `pair x (u ++ w)`
  have hkey : ∀ x u w : List Bool, h2 (pair (pair x u) w) = pair x (u ++ w) := by
    intro x u w
    have hx : (d ∘ d) (pair (pair x u) w) = x := by
      simp only [Function.comp_apply, hdx]
    have hc : (C ∘ h1) (pair (pair x u) w) = u ++ w := by
      simp only [Function.comp_apply, h1eq, hdx, hex, hCx]
    rw [h2eq, hx, hc]
  have hW1 := MPP.Solutions.Pnp008.main E h2 hE hh2
  have hW2 := MPP.Solutions.Pnp008.main V h2 hV hh2
  have hW : InP (fun y => E (h2 y) && V (h2 y)) := MPP.Solutions.Pnp011.main _ _ hW1 hW2
  have hNP : InNP (fun z => decide (∃ w : List Bool,
      w.length ≤ p.eval z.length ∧ (E (h2 (pair z w)) && V (h2 (pair z w))) = true)) := by
    refine ⟨fun y => E (h2 y) && V (h2 y), hW, p, fun z => ?_⟩
    exact decide_eq_true_iff
  refine ⟨_, hPNP _ hNP, fun x u => ?_⟩
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨w, _, hw⟩
    rw [hkey, Bool.and_eq_true] at hw
    exact ⟨w, (hEx x (u ++ w)).1 hw.1, hw.2⟩
  · rintro ⟨t, ht, hVt⟩
    refine ⟨t, ?_, ?_⟩
    · calc t.length ≤ (u ++ t).length := by simp
        _ = p.eval x.length := ht
        _ ≤ p.eval (pair x u).length := eval_mono p (length_le_pair x u)
    · rw [hkey, Bool.and_eq_true]
      exact ⟨(hEx x (u ++ t)).2 ht, hVt⟩

end MPP.Solutions.Pnp070
