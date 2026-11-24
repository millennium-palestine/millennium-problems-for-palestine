import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp033
import MPP.Solutions.Pnp051

namespace MPP.Solutions.Pnp050

open MPP.PvsNP Turing

theorem main : ∀ p : Polynomial ℕ, ∃ E : Lang, InP E ∧
    ∀ x w : List Bool, E (pair x w) = true ↔ w.length = p.eval x.length := by
  intro p
  obtain ⟨U, ⟨hU⟩, hUx⟩ := MPP.Solutions.Pnp033.main p
  obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨h1, ⟨hh1⟩, hh1z⟩ :=
    MPP.Solutions.Pnp026.main (U ∘ d) e (MPP.Solutions.Pnp006.main hd hU) ⟨he⟩
  obtain ⟨C1, hC1, hC1z⟩ := MPP.Solutions.Pnp028.main
  obtain ⟨C2, hC2, hC2z⟩ := MPP.Solutions.Pnp051.main
  have hE0 : InP (fun y => C1 y && C2 y) := MPP.Solutions.Pnp011.main C1 C2 hC1 hC2
  have hE : InP (fun y => (fun z => C1 z && C2 z) (h1 y)) :=
    MPP.Solutions.Pnp008.main _ h1 hE0 hh1
  refine ⟨fun y => (fun z => C1 z && C2 z) (h1 y), hE, fun x w => ?_⟩
  simp only [hh1z, Function.comp_apply, hdx, hex, hUx, Bool.and_eq_true, hC1z, hC2z,
    List.length_replicate]
  exact ⟨fun ⟨a, b⟩ => by omega, fun h => ⟨by omega, by omega⟩⟩

end MPP.Solutions.Pnp050
