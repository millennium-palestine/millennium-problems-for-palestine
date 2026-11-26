import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp237

namespace MPP.Solutions.Pnp238

open MPP.PvsNP Turing

theorem main : ∀ a b : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    ∃ s : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
      ∀ x w : List Bool,
        s (pair x w) = pair x (w ++ [(List.range (x.length + 1)).any (fun m =>
          w.getD (a (pair x (List.replicate m true))).length false &&
            w.getD (b (pair x (List.replicate m true))).length false)]) := by
  intro a b ha hb
  obtain ⟨f, hf, hfeq⟩ := MPP.Solutions.Pnp237.main a b ha hb
  obtain ⟨d, hd, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, he, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨c, hc, hceq⟩ := MPP.Solutions.Pnp127.main e f he hf
  obtain ⟨s, hs, hseq⟩ := MPP.Solutions.Pnp237.pairP hd hc
  refine ⟨s, hs, fun x w => ?_⟩
  rw [hseq, hceq, hdeq, heeq, hfeq]

end MPP.Solutions.Pnp238
