import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp045

namespace MPP.Solutions.Pnp044

open MPP.PvsNP Turing

/-- Unpadding a witness of the form `replicate k false ++ true :: w` gives back `w`. -/
theorem unpad_padded (k : ℕ) (w : List Bool) :
    ((List.replicate k false ++ true :: w).dropWhile fun b => !b).tail = w := by
  induction k with
  | zero => simp
  | succ k _ => simp [List.replicate_succ]

/-- Unpadding never returns a list longer than the input minus one. -/
theorem unpad_length (w : List Bool) :
    ((w.dropWhile fun b => !b).tail).length ≤ w.length - 1 := by
  rw [List.length_tail]
  exact Nat.sub_le_sub_right (List.length_dropWhile_le _ _) 1

theorem main : ∀ L : Lang, InNP L → ∃ V : Lang, InP V ∧ ∃ p : Polynomial ℕ, ∀ x : List Bool,
    (L x = true ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) := by
  intro L hL
  obtain ⟨V0, hV0, p0, hp0⟩ := hL
  obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨g, ⟨hg⟩, hgw⟩ := MPP.Solutions.Pnp045.main
  obtain ⟨h, ⟨hh⟩, hhz⟩ :=
    MPP.Solutions.Pnp026.main d (g ∘ e) ⟨hd⟩ (MPP.Solutions.Pnp006.main he hg)
  have hVI : InP (fun y => V0 (h y)) := MPP.Solutions.Pnp008.main V0 h hV0 hh
  have key : ∀ x w : List Bool, h (pair x w) = pair x (g w) := by
    intro x w
    rw [hhz]
    simp only [Function.comp_apply, hdx, hex]
  refine ⟨fun y => V0 (h y), hVI, p0 + 1, fun x => ?_⟩
  constructor
  · intro hL
    obtain ⟨w, hw, hVw⟩ := (hp0 x).1 hL
    refine ⟨List.replicate (p0.eval x.length - w.length) false ++ true :: w, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate, List.length_cons,
        Polynomial.eval_add, Polynomial.eval_one]
      omega
    · dsimp only
      rw [key, hgw, unpad_padded]
      exact hVw
  · rintro ⟨w', hw'len, hVw'⟩
    refine (hp0 x).2 ⟨g w', ?_, ?_⟩
    · rw [hgw]
      have hl := unpad_length w'
      rw [hw'len, Polynomial.eval_add, Polynomial.eval_one] at hl
      omega
    · dsimp only at hVw'
      rw [key] at hVw'
      exact hVw'

end MPP.Solutions.Pnp044
