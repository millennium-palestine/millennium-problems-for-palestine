import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp012
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp033
import MPP.Solutions.Pnp061
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp136

namespace MPP.Solutions.Pnp232

open MPP.PvsNP Turing

theorem main : ∀ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    (∀ x w : List Bool, ∃ b : Bool, s (pair x w) = pair x (w ++ [b])) →
    ∀ p : Polynomial ℕ, ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ x w : List Bool, T (pair x w) = s^[p.eval (pair x w).length] (pair x w) := by
  intro s hs hpair p
  -- padding z ↦ replicate (|z|+1) false
  obtain ⟨U, ⟨hU⟩, hUz⟩ := MPP.Solutions.Pnp033.main (Polynomial.X + 1)
  have hU' : ∀ z : List Bool, U z = List.replicate (z.length + 1) false := by
    intro z
    rw [hUz z]
    simp
  -- s' z = take (|z|+1) (s z ++ padding), total, with exact growth by one
  obtain ⟨hs0⟩ := hs
  obtain ⟨A, ⟨hA⟩, hAz⟩ := MPP.Solutions.Pnp127.main s U ⟨hs0⟩ ⟨hU⟩
  obtain ⟨P, ⟨hP⟩, hPz⟩ := MPP.Solutions.Pnp026.main A U ⟨hA⟩ ⟨hU⟩
  obtain ⟨t, ⟨ht⟩, htz⟩ := MPP.Solutions.Pnp136.main
  obtain ⟨hcomp⟩ := MPP.Solutions.Pnp006.main hP ht
  have hstep : ∀ z : List Bool, ((t ∘ P) z) = (s z ++ U z).take (z.length + 1) := by
    intro z
    simp only [Function.comp_apply]
    rw [hPz z, htz, hAz z, hU' z]
    simp
  have hlen : ∀ z : List Bool, ((t ∘ P) z).length = z.length + 1 := by
    intro z
    rw [hstep z, List.length_take, List.length_append, hU' z, List.length_replicate]
    omega
  obtain ⟨T, ⟨hT⟩, hTz⟩ := MPP.Solutions.Pnp061.main (t ∘ P) ⟨hcomp⟩ hlen p
  refine ⟨T, ⟨hT⟩, fun x w => ?_⟩
  rw [hTz]
  -- on pair encodings the total map agrees with s, and the iterates stay pair encodings
  have key : ∀ n : ℕ, ∃ v : List Bool, s^[n] (pair x w) = pair x v ∧
      (t ∘ P)^[n] (pair x w) = s^[n] (pair x w) := by
    intro n
    induction n with
    | zero => exact ⟨w, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨v, hv, hiter⟩ := ih
      obtain ⟨b, hb⟩ := hpair x v
      refine ⟨v ++ [b], ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hv, hb]
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hiter, hv, hstep, hb]
        exact List.take_left' (by simp only [MPP.Solutions.Pnp012.main, List.length_append,
          List.length_singleton]; omega)
  obtain ⟨_, _, h⟩ := key (p.eval (pair x w).length)
  exact h

end MPP.Solutions.Pnp232
