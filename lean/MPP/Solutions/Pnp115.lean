import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp063
import MPP.Solutions.Pnp066
import MPP.Solutions.Pnp117
import MPP.Solutions.Pnp118
import MPP.Solutions.Pnp120

namespace MPP.Solutions.Pnp115

open MPP.PvsNP Turing

/-- Applying the tail map `k` times drops the first `k` symbols. -/
theorem tail_iter (k : ℕ) : ∀ l : List Bool, (List.tail)^[k] l = l.drop k := by
  induction k with
  | zero => intro l; simp
  | succ k ih =>
      intro l
      rw [Function.iterate_succ_apply, ih]
      cases l <;> simp [List.drop_succ_cons]

theorem main : ∀ g : Lang, InP g → ∀ k : ℕ, ∃ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
    ∀ x : List Bool, f x = List.ofFn (fun i : Fin (x.length + 1 - (k + 1)) =>
      g ((x.drop (i : ℕ)).take (k + 1))) := by
  intro g hg k
  -- the window of the pair (x, u) and the one-bit step z ↦ z ++ [window bit]
  obtain ⟨D, ⟨hD⟩, hDeq⟩ := MPP.Solutions.Pnp120.main
  obtain ⟨T, ⟨hT⟩, hTeq⟩ := MPP.Solutions.Pnp118.main (k + 1)
  obtain ⟨hWD⟩ := MPP.Solutions.Pnp006.main hD hT
  have hng : InP (fun y => !g y) := MPP.Solutions.Pnp004.main g hg
  have hL : InP (fun z => !g (T (D z))) :=
    MPP.Solutions.Pnp008.main (fun y => !g y) (T ∘ D) hng hWD
  obtain ⟨S, ⟨hS⟩, hseq⟩ := MPP.Solutions.Pnp060.main (fun z => !g (T (D z))) hL
  have hSeq : ∀ z, S z = z ++ [g (T (D z))] := fun z => by
    rw [hseq]
    simp
  have hSlen : ∀ z, (S z).length = z.length + 1 := fun z => by
    rw [hSeq]
    simp
  -- iterate the step on unary counts: T (pair z (replicate m false)) = S^[m] z
  obtain ⟨Tit, ⟨hTit⟩, hit⟩ := MPP.Solutions.Pnp066.main S ⟨hS⟩ hSlen
  -- the count x.length + 1 - (k + 1) as a unary string, from the input length
  obtain ⟨Lg, ⟨hLg⟩, hLgeq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨Tl, ⟨hTl⟩, hTleq⟩ := MPP.Solutions.Pnp117.main
  have hTl' : Tl = List.tail := funext hTleq
  obtain ⟨Dk, ⟨hDk⟩, hDkeq⟩ := MPP.Solutions.Pnp063.main Tl ⟨hTl⟩ k
  have hCnt : ∀ x : List Bool, Dk (Lg x) = List.replicate (x.length + 1 - (k + 1)) false := by
    intro x
    rw [hDkeq, hTl', tail_iter, hLgeq, List.drop_replicate]
    congr 1
    omega
  -- the input x becomes the pair (pair x [], replicate m false)
  obtain ⟨Gz, ⟨hGz⟩, hGzeq⟩ := MPP.Solutions.Pnp030.main 0
  obtain ⟨P1, ⟨hP1⟩, hP1eq⟩ := MPP.Solutions.Pnp026.main id Gz MPP.Solutions.Pnp037.main ⟨hGz⟩
  have hP1x : ∀ x, P1 x = pair x [] := fun x => by
    rw [hP1eq, hGzeq]
    simp
  obtain ⟨Fm, ⟨hFm⟩, hFmeq⟩ :=
    MPP.Solutions.Pnp026.main P1 (Dk ∘ Lg) ⟨hP1⟩ (MPP.Solutions.Pnp006.main hLg hDk)
  have hFx : ∀ x, Fm x = pair (pair x []) (List.replicate (x.length + 1 - (k + 1)) false) :=
    fun x => by
      rw [hFmeq, Function.comp_apply, hP1x, hCnt]
  have hTF : ∀ x, Tit (Fm x) = S^[x.length + 1 - (k + 1)] (pair x []) := fun x => by
    rw [hFx, hit]
  -- the iterates list the windows
  have hwin : ∀ (m : ℕ) (x : List Bool), S^[m] (pair x []) =
      pair x (List.ofFn (fun i : Fin m => g ((x.drop (i : ℕ)).take (k + 1)))) := by
    intro m x
    induction m with
    | zero => simp [pair]
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih, hSeq, hDeq, List.length_ofFn, hTeq,
          List.ofFn_succ']
        simp [pair, List.append_assoc]
  -- the second component of the pair is the list of windows
  obtain ⟨E, ⟨hE⟩, hEeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨hTF'⟩ := MPP.Solutions.Pnp006.main hFm hTit
  refine ⟨E ∘ Tit ∘ Fm, MPP.Solutions.Pnp006.main hTF' hE, fun x => ?_⟩
  show E (Tit (Fm x)) = _
  rw [hTF, hwin, hEeq]

end MPP.Solutions.Pnp115
