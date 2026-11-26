import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp093
import MPP.Solutions.Pnp122
import MPP.Solutions.Pnp136

namespace MPP.Solutions.Pnp226

open Turing MPP.PvsNP

theorem comp_poly {f g : List Bool → List Bool}
    (hf : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f))
    (hg : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g)) :
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun z => g (f z))) := by
  obtain ⟨hf'⟩ := hf
  obtain ⟨hg'⟩ := hg
  exact MPP.Solutions.Pnp006.main hf' hg'

theorem pair_poly {f g : List Bool → List Bool}
    (hf : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f))
    (hg : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g)) :
    ∃ h : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) h) ∧
      ∀ z : List Bool, h z = pair (f z) (g z) :=
  MPP.Solutions.Pnp026.main f g hf hg

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool,
    L (pair x w) = decide (∀ b ∈ w.take (x.count true), b = true) := by
  obtain ⟨Dec, hDec, hDecEq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨Wit, hWit, hWitEq⟩ := MPP.Solutions.Pnp025.main
  have hCnt := MPP.Solutions.Pnp093.main
  obtain ⟨Tk, hTk, hTkEq⟩ := MPP.Solutions.Pnp136.main
  -- the unary count of the instance
  obtain ⟨Mk, hMk, hMkEq⟩ : ∃ Mk : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) Mk) ∧
      ∀ z : List Bool, Mk z = List.replicate ((Dec z).count true) true :=
    ⟨fun z => List.replicate ((Dec z).count true) true, comp_poly hDec hCnt, fun z => rfl⟩
  -- the witness prefix of that length
  obtain ⟨PW, hPW, hPWEq⟩ := pair_poly hWit hMk
  obtain ⟨TW, hTW, hTWEq⟩ : ∃ TW : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) TW) ∧
      ∀ z : List Bool, TW z = (Wit z).take (Mk z).length :=
    ⟨fun z => Tk (PW z), comp_poly hPW hTk, fun z => by
      show Tk (PW z) = _
      rw [hPWEq z]
      exact hTkEq _ _⟩
  -- the all-true test is in P, and P is closed under preprocessing by TW
  have hP : InP (fun y : List Bool => decide (∀ b ∈ y, b = true)) := MPP.Solutions.Pnp122.main
  obtain ⟨hTW'⟩ := hTW
  have hL := MPP.Solutions.Pnp008.main (fun y : List Bool => decide (∀ b ∈ y, b = true)) TW hP hTW'
  refine ⟨_, hL, fun x w => ?_⟩
  show decide (∀ b ∈ TW (pair x w), b = true) = _
  rw [hTWEq, hWitEq, hMkEq, hDecEq, List.length_replicate]

end MPP.Solutions.Pnp226
