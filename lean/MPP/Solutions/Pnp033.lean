import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp031
import MPP.Solutions.Pnp032

namespace MPP.Solutions.Pnp033

open Turing

/-- The `n`-th power of the input length, in unary, is polynomial-time. Induction on `n`:
the step multiplies the unary string of `|x|^n` by the unary length of `x` (pnp-032). -/
theorem powG : ∀ n : ℕ, ∃ G : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) G) ∧
    ∀ x : List Bool, G x = List.replicate (x.length ^ n) false
  | 0 => by
    obtain ⟨C, ⟨hC⟩, hCx⟩ := MPP.Solutions.Pnp030.main 1
    exact ⟨C, ⟨hC⟩, fun x => by rw [hCx x, pow_zero]⟩
  | n + 1 => by
    obtain ⟨G, ⟨hG⟩, hGx⟩ := powG n
    obtain ⟨L, ⟨hL⟩, hLx⟩ := MPP.Solutions.Pnp029.main
    obtain ⟨M, ⟨hM⟩, hMp⟩ := MPP.Solutions.Pnp032.main
    obtain ⟨h, ⟨hh⟩, hhz⟩ := MPP.Solutions.Pnp026.main G L ⟨hG⟩ ⟨hL⟩
    obtain ⟨k⟩ := MPP.Solutions.Pnp006.main hh hM
    refine ⟨fun x => M (h x), ⟨k⟩, fun x => ?_⟩
    dsimp only
    rw [hhz x, hMp, hGx x, hLx x]
    simp [pow_succ]

theorem main : ∀ p : Polynomial ℕ, ∃ g : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) ∧
    ∀ x : List Bool, g x = List.replicate (p.eval x.length) false := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨g, ⟨hg⟩, hgx⟩ := hp
    obtain ⟨g', ⟨hg'⟩, hg'x⟩ := hq
    obtain ⟨h, ⟨hh⟩, hhz⟩ := MPP.Solutions.Pnp026.main g g' ⟨hg⟩ ⟨hg'⟩
    obtain ⟨E, ⟨hE⟩, hEp⟩ := MPP.Solutions.Pnp031.main
    obtain ⟨k⟩ := MPP.Solutions.Pnp006.main hh hE
    refine ⟨fun x => E (h x), ⟨k⟩, fun x => ?_⟩
    dsimp only
    rw [hhz x, hEp, hgx x, hg'x x]
    simp [Polynomial.eval_add]
  | monomial n a =>
    obtain ⟨G, ⟨hG⟩, hGx⟩ := powG n
    obtain ⟨C, ⟨hC⟩, hCx⟩ := MPP.Solutions.Pnp030.main a
    obtain ⟨M, ⟨hM⟩, hMp⟩ := MPP.Solutions.Pnp032.main
    obtain ⟨h, ⟨hh⟩, hhz⟩ := MPP.Solutions.Pnp026.main C G ⟨hC⟩ ⟨hG⟩
    obtain ⟨k⟩ := MPP.Solutions.Pnp006.main hh hM
    refine ⟨fun x => M (h x), ⟨k⟩, fun x => ?_⟩
    dsimp only
    rw [hhz x, hMp, hCx x, hGx x]
    simp [Polynomial.eval_monomial]

end MPP.Solutions.Pnp033
