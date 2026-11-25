import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp052
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp066
import MPP.Solutions.Pnp120
import MPP.Solutions.Pnp136

namespace MPP.Solutions.Pnp137

open MPP.PvsNP Turing

theorem main : ∀ g : Lang, InP g → ∃ F : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) F) ∧
    ∀ x u : List Bool, F (pair x u) = List.ofFn (fun i : Fin (x.length + 1 - (u.length + 1)) =>
      g ((x.drop (i : ℕ)).take (u.length + 1))) := by
  intro g hg
  -- the building blocks: drop and take by a length read from the second component
  obtain ⟨D, ⟨hD⟩, hDeq⟩ := MPP.Solutions.Pnp120.main
  obtain ⟨T, ⟨hT⟩, hTeq⟩ := MPP.Solutions.Pnp136.main
  obtain ⟨d, ⟨hd⟩, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨C, ⟨hC⟩, hCeq⟩ := MPP.Solutions.Pnp052.main
  obtain ⟨Lg, ⟨hLg⟩, hLgeq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨c1, ⟨hc1⟩, hc1eq⟩ := MPP.Solutions.Pnp030.main 1
  obtain ⟨c0, ⟨hc0⟩, hc0eq⟩ := MPP.Solutions.Pnp030.main 0
  -- the window read from a state z = pair (pair x u) w: Q z = pair (x.drop |w|) (u ++ [false])
  obtain ⟨K1, ⟨hK1⟩, hK1eq⟩ := MPP.Solutions.Pnp026.main (d ∘ d) e
    (MPP.Solutions.Pnp006.main hd hd) ⟨he⟩
  obtain ⟨hA⟩ := MPP.Solutions.Pnp006.main hK1 hD
  obtain ⟨K2, ⟨hK2⟩, hK2eq⟩ := MPP.Solutions.Pnp026.main (e ∘ d) c1
    (MPP.Solutions.Pnp006.main hd he) ⟨hc1⟩
  obtain ⟨hB⟩ := MPP.Solutions.Pnp006.main hK2 hC
  obtain ⟨Q, ⟨hQ⟩, hQeq⟩ := MPP.Solutions.Pnp026.main (D ∘ K1) (C ∘ K2) ⟨hA⟩ ⟨hB⟩
  obtain ⟨hW⟩ := MPP.Solutions.Pnp006.main hQ hT
  have hWeq : ∀ x u w : List Bool, (T ∘ Q) (pair (pair x u) w) =
      (x.drop w.length).take (u.length + 1) := by
    intro x u w
    simp [Function.comp_apply, hQeq, hK1eq, hK2eq, hTeq, hDeq, hCeq, hdeq, heeq, hc1eq]
  -- one-bit extension: z ↦ z ++ [g (window of z)]
  have hnotg : InP (fun y => !g y) := MPP.Solutions.Pnp004.main g hg
  have hL : InP (fun z => !g ((T ∘ Q) z)) :=
    MPP.Solutions.Pnp008.main (fun y => !g y) (T ∘ Q) hnotg hW
  obtain ⟨S, ⟨hS⟩, hSeq⟩ := MPP.Solutions.Pnp060.main (fun z => !g ((T ∘ Q) z)) hL
  have hSeq' : ∀ z, S z = z ++ [g ((T ∘ Q) z)] := fun z => by
    rw [hSeq]
    simp
  have hSlen : ∀ z, (S z).length = z.length + 1 := fun z => by
    rw [hSeq']
    simp
  -- the iterates list the windows
  have hwin : ∀ (m : ℕ) (x u : List Bool), S^[m] (pair (pair x u) []) =
      pair (pair x u) (List.ofFn (fun i : Fin m => g ((x.drop (i : ℕ)).take (u.length + 1)))) := by
    intro m x u
    induction m with
    | zero => simp [pair]
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih, hSeq', hWeq, List.length_ofFn, List.ofFn_succ']
        simp [pair, List.append_assoc]
  -- the start state pair (pair x u) [], and the unary count x.length - u.length
  obtain ⟨P1, ⟨hP1⟩, hP1eq⟩ := MPP.Solutions.Pnp026.main id c0 MPP.Solutions.Pnp037.main ⟨hc0⟩
  have hP1x : ∀ y, P1 y = pair y [] := fun y => by
    rw [hP1eq, hc0eq]
    simp
  obtain ⟨Fm, ⟨hFm⟩, hFmeq⟩ :=
    MPP.Solutions.Pnp026.main P1 (Lg ∘ D) ⟨hP1⟩ (MPP.Solutions.Pnp006.main hD hLg)
  have hFx : ∀ x u : List Bool, Fm (pair x u) =
      pair (pair (pair x u) []) (List.replicate (x.length + 1 - (u.length + 1)) false) := by
    intro x u
    rw [hFmeq, Function.comp_apply, hP1x, hDeq, hLgeq, List.length_drop,
      show x.length + 1 - (u.length + 1) = x.length - u.length by omega]
  -- iterate the extension on the count
  obtain ⟨Tit, ⟨hTit⟩, hit⟩ := MPP.Solutions.Pnp066.main S ⟨hS⟩ hSlen
  obtain ⟨hTF⟩ := MPP.Solutions.Pnp006.main hFm hTit
  refine ⟨e ∘ Tit ∘ Fm, MPP.Solutions.Pnp006.main hTF he, fun x u => ?_⟩
  show e (Tit (Fm (pair x u))) = _
  rw [hFx, hit, hwin, heeq]

end MPP.Solutions.Pnp137
