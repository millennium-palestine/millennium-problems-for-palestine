import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp120
import MPP.Solutions.Pnp136

namespace MPP.Solutions.Pnp138

open MPP.PvsNP Turing

theorem main : ∀ g : Lang, InP g → ∃ S : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) S) ∧
    (∀ z : List Bool, (S z).length = z.length + 1) ∧
    ∀ x c out : List Bool, S (pair (pair x c) out) =
      pair (pair x c) (out ++ [g ((x.drop out.length).take c.length)]) := by
  intro g hg
  -- decoders: d takes the first component, e takes the second component
  obtain ⟨d, ⟨hd⟩, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨D, ⟨hD⟩, hDeq⟩ := MPP.Solutions.Pnp120.main
  obtain ⟨T, ⟨hT⟩, hTeq⟩ := MPP.Solutions.Pnp136.main
  -- the input x is d (d z), the output so far is e z, the width is e (d z)
  have hdd := MPP.Solutions.Pnp006.main hd hd
  obtain ⟨h1, ⟨hh1⟩, hh1eq⟩ :=
    MPP.Solutions.Pnp026.main (d ∘ d) e hdd ⟨he⟩
  -- the suffix of x after the output so far
  have hDD := MPP.Solutions.Pnp006.main hh1 hD
  have hed := MPP.Solutions.Pnp006.main hd he
  obtain ⟨h2, ⟨hh2⟩, hh2eq⟩ :=
    MPP.Solutions.Pnp026.main (D ∘ h1) (e ∘ d) hDD hed
  -- the window: take of the width from the suffix
  obtain ⟨hTW⟩ := MPP.Solutions.Pnp006.main hh2 hT
  have hInP : InP (fun z => g ((T ∘ h2) z)) :=
    MPP.Solutions.Pnp008.main g (T ∘ h2) hg hTW
  have hneg : InP (fun z => !g ((T ∘ h2) z)) :=
    MPP.Solutions.Pnp004.main (fun z => g ((T ∘ h2) z)) hInP
  obtain ⟨S, ⟨hS⟩, hSeq⟩ := MPP.Solutions.Pnp060.main (fun z => !g ((T ∘ h2) z)) hneg
  have hwin : ∀ x c out : List Bool,
      (T ∘ h2) (pair (pair x c) out) = (x.drop out.length).take c.length := by
    intro x c out
    simp only [Function.comp, hh2eq, hTeq, hh1eq, hDeq, hdeq, heeq]
  refine ⟨S, ⟨hS⟩, fun z => ?_, fun x c out => ?_⟩
  · rw [hSeq]
    simp
  · rw [hSeq, hwin]
    simp [pair, List.append_assoc]

end MPP.Solutions.Pnp138
