import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp044
import MPP.Solutions.Pnp050

namespace MPP.Solutions.Pnp074

open MPP.PvsNP Turing

theorem main : (∀ (V : Lang) (p : Polynomial ℕ), InP V →
    ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
        (f x).length = p.eval x.length ∧ V (pair x (f x)) = true) →
    PEqualsNP := by
  intro H
  unfold PEqualsNP
  intro L hL
  obtain ⟨V, hV, p, hp⟩ := MPP.Solutions.Pnp044.main L hL
  obtain ⟨f, ⟨hf⟩, hfx⟩ := H V p hV
  obtain ⟨E, hE, hEx⟩ := MPP.Solutions.Pnp050.main p
  -- the map x ↦ pair x (f x), polynomial-time by pnp-026
  obtain ⟨h, ⟨hh⟩, hhx⟩ := MPP.Solutions.Pnp026.main id f MPP.Solutions.Pnp037.main ⟨hf⟩
  have hpair : ∀ x, h x = pair x (f x) := fun x => hhx x
  -- L x holds exactly when the pair of x and the found witness passes both checks
  have hiff : ∀ x, L x = true ↔ (E (pair x (f x)) && V (pair x (f x))) = true := by
    intro x
    rw [Bool.and_eq_true]
    constructor
    · intro hl
      obtain ⟨w, hw, hVw⟩ := (hp x).1 hl
      obtain ⟨hlen, hVf⟩ := hfx x ⟨w, hw, hVw⟩
      exact ⟨(hEx x (f x)).2 hlen, hVf⟩
    · rintro ⟨hE', hVf⟩
      exact (hp x).2 ⟨f x, (hEx x (f x)).1 hE', hVf⟩
  have hLfun : L = fun x => E (h x) && V (h x) := by
    funext x
    show L x = (E (h x) && V (h x))
    rw [hpair x]
    exact Bool.eq_iff_iff.mpr (hiff x)
  have hW1 := MPP.Solutions.Pnp008.main E h hE hh
  have hW2 := MPP.Solutions.Pnp008.main V h hV hh
  rw [hLfun]
  exact MPP.Solutions.Pnp011.main _ _ hW1 hW2

end MPP.Solutions.Pnp074
