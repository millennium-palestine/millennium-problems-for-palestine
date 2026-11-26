import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp052
import MPP.Solutions.Pnp117
import MPP.Solutions.Pnp120
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp136
import MPP.Solutions.Pnp228

namespace MPP.Solutions.Pnp235

open Turing MPP.PvsNP

theorem main : ∀ h : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) h) →
    ∀ g : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) →
      ∃ f : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
        ∀ (x w : List Bool) (b : Bool), g (pair x w) = [b] →
          f (pair x w) = pair x (w.set (h x).length b) := by
  intro h hh g hg
  obtain ⟨Dec, hDec, hDecEq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨Wit, hWit, hWitEq⟩ := MPP.Solutions.Pnp025.main
  -- the index map: h applied to the decoded instance
  obtain ⟨Mk, hMk, hMkEq⟩ : ∃ Mk : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) Mk) ∧
      ∀ z : List Bool, Mk z = h (Dec z) :=
    ⟨fun z => h (Dec z), MPP.Solutions.Pnp228.comp_poly hDec hh, fun z => rfl⟩
  obtain ⟨Tk, hTk, hTkEq⟩ := MPP.Solutions.Pnp136.main
  obtain ⟨Dr, hDr, hDrEq⟩ := MPP.Solutions.Pnp120.main
  obtain ⟨Tl, hTl, hTlEq⟩ := MPP.Solutions.Pnp117.main
  obtain ⟨Cc, hCc, hCcEq⟩ := MPP.Solutions.Pnp052.main
  -- the pair (witness, index) and its take and drop by the index
  obtain ⟨PW, hPW, hPWEq⟩ := MPP.Solutions.Pnp228.pair_poly hWit hMk
  obtain ⟨TW, hTW, hTWEq⟩ : ∃ TW : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) TW) ∧
      ∀ z : List Bool, TW z = (Wit z).take (Mk z).length :=
    ⟨fun z => Tk (PW z), MPP.Solutions.Pnp228.comp_poly hPW hTk, fun z => by
      show Tk (PW z) = _
      rw [hPWEq z]
      exact hTkEq _ _⟩
  obtain ⟨DW, hDW, hDWEq⟩ : ∃ DW : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) DW) ∧
      ∀ z : List Bool, DW z = (Wit z).drop (Mk z).length :=
    ⟨fun z => Dr (PW z), MPP.Solutions.Pnp228.comp_poly hPW hDr, fun z => by
      show Dr (PW z) = _
      rw [hPWEq z]
      exact hDrEq _ _⟩
  obtain ⟨TD, hTD, hTDEq⟩ : ∃ TD : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) TD) ∧
      ∀ z : List Bool, TD z = Tl (DW z) :=
    ⟨fun z => Tl (DW z), MPP.Solutions.Pnp228.comp_poly hDW hTl, fun z => rfl⟩
  obtain ⟨PG, hPG, hPGEq⟩ := MPP.Solutions.Pnp228.pair_poly hg hTD
  obtain ⟨CG, hCG, hCGEq⟩ : ∃ CG : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) CG) ∧
      ∀ z : List Bool, CG z = g z ++ (DW z).tail :=
    ⟨fun z => Cc (PG z), MPP.Solutions.Pnp228.comp_poly hPG hCc, fun z => by
      show Cc (PG z) = _
      rw [hPGEq z, hTDEq z, hTlEq (DW z)]
      exact hCcEq _ _⟩
  obtain ⟨PC, hPC, hPCEq⟩ := MPP.Solutions.Pnp228.pair_poly hCG hDW
  obtain ⟨HD, hHD, hHDEq⟩ : ∃ HD : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) HD) ∧
      ∀ z : List Bool, HD z = (g z ++ (DW z).tail).take (DW z).length :=
    ⟨fun z => Tk (PC z), MPP.Solutions.Pnp228.comp_poly hPC hTk, fun z => by
      show Tk (PC z) = _
      rw [hPCEq z, hCGEq z]
      exact hTkEq _ _⟩
  -- the new witness: the prefix, then the rebuilt rest
  obtain ⟨U, hU, hUEq⟩ := MPP.Solutions.Pnp127.main TW HD hTW hHD
  obtain ⟨F, hF, hFEq⟩ := MPP.Solutions.Pnp228.pair_poly hDec hU
  refine ⟨F, hF, fun x w b hgb => ?_⟩
  have hT : TW (pair x w) = w.take (h x).length := by
    rw [hTWEq, hWitEq, hMkEq, hDecEq]
  have hD : DW (pair x w) = w.drop (h x).length := by
    rw [hDWEq, hWitEq, hMkEq, hDecEq]
  have hH : HD (pair x w) = (b :: (w.drop (h x).length).tail).take (w.drop (h x).length).length := by
    rw [hHDEq, hD, hgb, List.singleton_append]
  rw [hFEq, hDecEq, hUEq, hT, hH, MPP.Solutions.Pnp228.set_eq_take_append]

end MPP.Solutions.Pnp235
