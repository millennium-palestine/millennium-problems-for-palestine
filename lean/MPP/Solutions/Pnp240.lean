import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp237

namespace MPP.Solutions.Pnp240

open MPP.PvsNP Turing

theorem main : ∀ a b : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    ∃ s : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
      ∀ x w : List Bool,
        s (pair x w) = pair x (w ++ [(List.range ((pair x (List.replicate w.length false)).length + 1)).any
          (fun m =>
            w.getD (a (pair (pair x (List.replicate w.length false)) (List.replicate m true))).length false &&
              w.getD (b (pair (pair x (List.replicate w.length false)) (List.replicate m true))).length false)]) := by
  intro a b ha hb
  obtain ⟨f, hf, hfeq⟩ := MPP.Solutions.Pnp237.main a b ha hb
  obtain ⟨d, hd, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, he, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨g, hg, hgeq⟩ := MPP.Solutions.Pnp029.main
  -- X z = pair (instance of z) (replicate |witness of z| false)
  obtain ⟨X, hX, hXeq⟩ := MPP.Solutions.Pnp237.pairP hd (MPP.Solutions.Pnp237.comp he hg)
  -- Y z = pair (X z) (witness of z): the instance pair x (replicate |w| false) with the witness w
  obtain ⟨Y, hY, hYeq⟩ := MPP.Solutions.Pnp237.pairP hX he
  -- the cell bit of pnp-237 at that instance
  obtain ⟨h, hh, hheq⟩ := MPP.Solutions.Pnp127.main e (f ∘ Y) he (MPP.Solutions.Pnp237.comp hY hf)
  obtain ⟨s, hs, hseq⟩ := MPP.Solutions.Pnp237.pairP hd hh
  refine ⟨s, hs, fun x w => ?_⟩
  simp only [hseq, hheq, Function.comp_apply, hYeq, hXeq, hdeq, heeq, hgeq, hfeq]

end MPP.Solutions.Pnp240
