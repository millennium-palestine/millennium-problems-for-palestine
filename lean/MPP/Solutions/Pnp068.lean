import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp056
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp070

namespace MPP.Solutions.Pnp068

open MPP.PvsNP Turing

/-- Appending a bit to the pair encoding appends it to the second component. -/
theorem pair_append_bit (x u : List Bool) (b : Bool) :
    pair x u ++ [b] = pair x (u ++ [b]) := by
  unfold pair
  simp [List.append_assoc]

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V → PEqualsNP →
    ∃ G : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) G) ∧
      ∀ x u : List Bool,
        ((∃ t : List Bool, (u ++ [false] ++ t).length = p.eval x.length ∧
            V (pair x (u ++ [false] ++ t)) = true) → G (pair x u) = pair x (u ++ [false])) ∧
        (¬ (∃ t : List Bool, (u ++ [false] ++ t).length = p.eval x.length ∧
            V (pair x (u ++ [false] ++ t)) = true) → G (pair x u) = pair x (u ++ [true])) := by
  intro V p hV hPNP
  obtain ⟨D, hD, hDx⟩ := MPP.Solutions.Pnp070.main V p hV hPNP
  obtain ⟨s, ⟨hs⟩, hsx⟩ := MPP.Solutions.Pnp056.main
  obtain ⟨G, ⟨hG⟩, hGz⟩ :=
    MPP.Solutions.Pnp060.main (fun y => D (s y)) (MPP.Solutions.Pnp008.main D s hD hs)
  refine ⟨G, ⟨hG⟩, fun x u => ?_⟩
  have hG' : G (pair x u) = pair x (u ++ [!D (pair x (u ++ [false]))]) := by
    have h := hGz (pair x u)
    simp only [hsx] at h
    rw [h, pair_append_bit]
  constructor
  · intro h
    have hd : D (pair x (u ++ [false])) = true := (hDx x (u ++ [false])).2 h
    rw [hG', hd]
    rfl
  · intro h
    have hd : D (pair x (u ++ [false])) = false := by
      cases hb : D (pair x (u ++ [false]))
      · rfl
      · exact absurd ((hDx x (u ++ [false])).1 hb) h
    rw [hG', hd]
    rfl

end MPP.Solutions.Pnp068
