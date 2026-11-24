import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp012
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp027

namespace MPP.Solutions.Pnp034

open MPP.PvsNP Turing

theorem main : ∀ L M : Lang, InNP L → InNP M → InNP (fun x => L x && M x) := by
  intro L M hL hM
  obtain ⟨V1, hV1, p1, hp1⟩ := hL
  obtain ⟨V2, hV2, p2, hp2⟩ := hM
  obtain ⟨C1, hC1, hC1i⟩ := MPP.Solutions.Pnp027.main p1
  obtain ⟨C2, hC2, hC2i⟩ := MPP.Solutions.Pnp027.main p2
  obtain ⟨d, ⟨hd⟩, hdz⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hez⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨hde⟩ := MPP.Solutions.Pnp006.main he hd
  obtain ⟨hee⟩ := MPP.Solutions.Pnp006.main he he
  obtain ⟨h1, ⟨hh1⟩, hh1z⟩ := MPP.Solutions.Pnp026.main d (d ∘ e) ⟨hd⟩ ⟨hde⟩
  obtain ⟨h2, ⟨hh2⟩, hh2z⟩ := MPP.Solutions.Pnp026.main d (e ∘ e) ⟨hd⟩ ⟨hee⟩
  have hV1' : InP (fun z => V1 (h1 z)) := MPP.Solutions.Pnp008.main V1 h1 hV1 hh1
  have hC1' : InP (fun z => C1 (h1 z)) := MPP.Solutions.Pnp008.main C1 h1 hC1 hh1
  have hV2' : InP (fun z => V2 (h2 z)) := MPP.Solutions.Pnp008.main V2 h2 hV2 hh2
  have hC2' : InP (fun z => C2 (h2 z)) := MPP.Solutions.Pnp008.main C2 h2 hC2 hh2
  have hW := MPP.Solutions.Pnp011.main _ _
    (MPP.Solutions.Pnp011.main _ _ hV1' hC1') (MPP.Solutions.Pnp011.main _ _ hV2' hC2')
  unfold InNP
  refine ⟨fun z => (V1 (h1 z) && C1 (h1 z)) && (V2 (h2 z) && C2 (h2 z)), hW, 2 * p1 + p2 + 2,
    fun x => ?_⟩
  show (L x && M x) = true ↔ _
  constructor
  · intro hLM
    rw [Bool.and_eq_true] at hLM
    obtain ⟨w1, hw1, hV1w⟩ := (hp1 x).1 hLM.1
    obtain ⟨w2, hw2, hV2w⟩ := (hp2 x).1 hLM.2
    refine ⟨pair w1 w2, ?_, ?_⟩
    · rw [MPP.Solutions.Pnp012.main w1 w2]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
      omega
    · simp only [hh1z, hh2z, Function.comp, hdz, hez]
      simp [hV1w, (hC1i x w1).2 hw1, hV2w, (hC2i x w2).2 hw2]
  · rintro ⟨w, hw, hW⟩
    simp only [hh1z, hh2z, Function.comp, hdz, hez, Bool.and_eq_true] at hW
    obtain ⟨⟨h1a, h1b⟩, h2a, h2b⟩ := hW
    rw [Bool.and_eq_true]
    exact ⟨(hp1 x).2 ⟨d w, (hC1i x (d w)).1 h1b, h1a⟩,
      (hp2 x).2 ⟨e w, (hC2i x (e w)).1 h2b, h2a⟩⟩

end MPP.Solutions.Pnp034
