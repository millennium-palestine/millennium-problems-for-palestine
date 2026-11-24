import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp072
import MPP.Solutions.Pnp081
import MPP.Solutions.Pnp082

namespace MPP.Solutions.Pnp083

open Turing MPP.PvsNP

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V → PEqualsNP →
    ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
        (f x).length = p.eval x.length ∧ V (pair x (f x)) = true ∧
        ∀ w : List Bool, w.length = p.eval x.length → V (pair x w) = true → ¬ (f x < w) := by
  intro V p hV hP
  have hinv : ∀ w : List Bool, (w.map (fun b => !b)).map (fun b => !b) = w := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih => simp only [List.map_cons, Bool.not_not, ih]
  -- the verifier with the witness complemented, and its polynomial-time membership in P
  obtain ⟨r, hr, hrf⟩ := MPP.Solutions.Pnp081.main
  obtain ⟨mr⟩ := hr
  have hV' : InP (fun z => V (r z)) := MPP.Solutions.Pnp008.main V r hV mr
  -- the least accepted witness of the complemented verifier, from pnp-072
  obtain ⟨f', hf', hf⟩ := MPP.Solutions.Pnp072.main (fun z => V (r z)) p hV' hP
  -- the map z ↦ pair [] z, then the complement of the whole string
  obtain ⟨c, hc, hcx⟩ := MPP.Solutions.Pnp030.main 0
  obtain ⟨h, hh, hhf⟩ := MPP.Solutions.Pnp026.main c id hc MPP.Solutions.Pnp037.main
  have hh' : ∀ z, h z = pair [] z := fun z => by simp [hhf z, hcx z]
  have hneg : ∀ u : List Bool, MPP.Solutions.Pnp081.negSuf (h u) = u.map (fun b => !b) := by
    intro u
    rw [hh' u]
    exact MPP.Solutions.Pnp081.negSuf_pair [] u
  obtain ⟨mh⟩ := hh
  obtain ⟨mf⟩ := hf'
  obtain ⟨mNH⟩ := MPP.Solutions.Pnp006.main mh MPP.Solutions.Pnp081.machine
  have hfin := MPP.Solutions.Pnp006.main mf mNH
  refine ⟨(MPP.Solutions.Pnp081.negSuf ∘ h) ∘ f', hfin, fun x hx => ?_⟩
  obtain ⟨w0, hw0, hV0⟩ := hx
  -- the complemented verifier accepts the complement of a witness of V
  have hex : ∃ w, w.length = p.eval x.length ∧ V (r (pair x w)) = true :=
    ⟨w0.map (fun b => !b), by simpa using hw0, by rw [hrf, hinv]; exact hV0⟩
  obtain ⟨hlen, hacc, hmin⟩ := hf x hex
  have hacc' : V (r (pair x (f' x))) = true := hacc
  rw [hrf] at hacc'
  have hfx : ((MPP.Solutions.Pnp081.negSuf ∘ h) ∘ f') x = (f' x).map (fun b => !b) := by
    simp only [Function.comp_apply, hneg]
  rw [hfx]
  refine ⟨by simpa using hlen, hacc', fun w hw hVw => ?_⟩
  have hVw' : V (r (pair x (w.map (fun b => !b)))) = true := by
    rw [hrf, hinv]
    exact hVw
  have hmin' := hmin (w.map (fun b => !b)) (by simpa using hw) hVw'
  have hord := MPP.Solutions.Pnp082.main (f' x) (w.map (fun b => !b)) (by simp [hlen, hw])
  rw [hinv w] at hord
  intro hlt
  exact hmin' (hord.mp hlt)

end MPP.Solutions.Pnp083
