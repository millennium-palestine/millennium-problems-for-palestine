import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp010
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp012
import MPP.Solutions.Pnp013
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp027

namespace MPP.Solutions.Pnp035

open MPP.PvsNP Turing

theorem main : ∀ L M : Lang, InNP L → InNP M → InNP (fun x => L x || M x) := by
  intro L M hL hM
  obtain ⟨V1, hV1, p1, hp1⟩ := hL
  obtain ⟨V2, hV2, p2, hp2⟩ := hM
  obtain ⟨C1, hC1, hC1i⟩ := MPP.Solutions.Pnp027.main p1
  obtain ⟨C2, hC2, hC2i⟩ := MPP.Solutions.Pnp027.main p2
  obtain ⟨d, ⟨hd⟩, hdz⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hez⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨hde⟩ := MPP.Solutions.Pnp006.main he hd
  obtain ⟨hee⟩ := MPP.Solutions.Pnp006.main he he
  obtain ⟨h, ⟨hh⟩, hhz⟩ := MPP.Solutions.Pnp026.main d (e ∘ e) ⟨hd⟩ ⟨hee⟩
  have hT : InP (fun z => (d (e z)).headD false) :=
    MPP.Solutions.Pnp008.main _ (d ∘ e) MPP.Solutions.Pnp013.main hde
  have hNT : InP (fun z => !((d (e z)).headD false)) := MPP.Solutions.Pnp004.main _ hT
  have hA1 : InP (fun z => V1 (h z) && C1 (h z)) :=
    MPP.Solutions.Pnp011.main _ _ (MPP.Solutions.Pnp008.main V1 h hV1 hh)
      (MPP.Solutions.Pnp008.main C1 h hC1 hh)
  have hA2 : InP (fun z => V2 (h z) && C2 (h z)) :=
    MPP.Solutions.Pnp011.main _ _ (MPP.Solutions.Pnp008.main V2 h hV2 hh)
      (MPP.Solutions.Pnp008.main C2 h hC2 hh)
  have hB1 : InP (fun z => (d (e z)).headD false && (V2 (h z) && C2 (h z))) :=
    MPP.Solutions.Pnp011.main _ _ hT hA2
  have hB2 : InP (fun z => !((d (e z)).headD false) && (V1 (h z) && C1 (h z))) :=
    MPP.Solutions.Pnp011.main _ _ hNT hA1
  have hW := MPP.Solutions.Pnp010.main _ _ hB1 hB2
  unfold InNP
  refine ⟨fun z => ((d (e z)).headD false && (V2 (h z) && C2 (h z))) ||
    (!((d (e z)).headD false) && (V1 (h z) && C1 (h z))), hW, p1 + p2 + 4, fun x => ?_⟩
  show (L x || M x) = true ↔ _
  constructor
  · intro hLM
    rw [Bool.or_eq_true] at hLM
    rcases hLM with hL' | hM'
    · obtain ⟨w1, hw1, hV1w⟩ := (hp1 x).1 hL'
      refine ⟨pair [false] w1, ?_, ?_⟩
      · rw [MPP.Solutions.Pnp012.main [false] w1]
        simp only [List.length_singleton, Polynomial.eval_add, Polynomial.eval_ofNat]
        omega
      · simp only [hhz, hdz, hez, Function.comp]
        simp [hV1w, (hC1i x w1).2 hw1]
    · obtain ⟨w2, hw2, hV2w⟩ := (hp2 x).1 hM'
      refine ⟨pair [true] w2, ?_, ?_⟩
      · rw [MPP.Solutions.Pnp012.main [true] w2]
        simp only [List.length_singleton, Polynomial.eval_add, Polynomial.eval_ofNat]
        omega
      · simp only [hhz, hdz, hez, Function.comp]
        simp [hV2w, (hC2i x w2).2 hw2]
  · rintro ⟨w, -, hw⟩
    simp only [hhz, hdz, hez, Function.comp, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hw
    rw [Bool.or_eq_true]
    rcases hw with ⟨-, h2a, h2b⟩ | ⟨-, h1a, h1b⟩
    · exact Or.inr ((hp2 x).2 ⟨e w, (hC2i x (e w)).1 h2b, h2a⟩)
    · exact Or.inl ((hp1 x).2 ⟨e w, (hC1i x (e w)).1 h1b, h1a⟩)

end MPP.Solutions.Pnp035
