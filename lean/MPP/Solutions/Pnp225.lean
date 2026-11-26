import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp052
import MPP.Solutions.Pnp093
import MPP.Solutions.Pnp117
import MPP.Solutions.Pnp120
import MPP.Solutions.Pnp126
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp136

namespace MPP.Solutions.Pnp225

open Turing MPP.PvsNP

theorem set_eq_take_append (w : List Bool) (k : ℕ) :
    w.take k ++ ((true :: (w.drop k).tail).take (w.drop k).length) = w.set k true := by
  induction w generalizing k with
  | nil => simp
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.set_cons_succ]
      rw [← ih k]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]

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

theorem main : ∃ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
    ∀ x w : List Bool, f (pair x w) = pair x (w.set (x.count true) true) := by
  obtain ⟨Dec, hDec, hDecEq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨Wit, hWit, hWitEq⟩ := MPP.Solutions.Pnp025.main
  have hCnt := MPP.Solutions.Pnp093.main
  obtain ⟨Tk, hTk, hTkEq⟩ := MPP.Solutions.Pnp136.main
  obtain ⟨Dr, hDr, hDrEq⟩ := MPP.Solutions.Pnp120.main
  obtain ⟨Tl, hTl, hTlEq⟩ := MPP.Solutions.Pnp117.main
  obtain ⟨Cs, hCs, hCsEq⟩ := MPP.Solutions.Pnp126.main [true]
  obtain ⟨Cc, hCc, hCcEq⟩ := MPP.Solutions.Pnp052.main
  have hId := MPP.Solutions.Pnp037.main
  -- the unary count of the instance
  obtain ⟨Mk, hMk, hMkEq⟩ : ∃ Mk : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) Mk) ∧
      ∀ z : List Bool, Mk z = List.replicate ((Dec z).count true) true :=
    ⟨fun z => List.replicate ((Dec z).count true) true, comp_poly hDec hCnt, fun z => rfl⟩
  -- the pair (witness, count) and its take and drop by the count
  obtain ⟨PW, hPW, hPWEq⟩ := pair_poly hWit hMk
  obtain ⟨TW, hTW, hTWEq⟩ : ∃ TW : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) TW) ∧
      ∀ z : List Bool, TW z = (Wit z).take (Mk z).length :=
    ⟨fun z => Tk (PW z), comp_poly hPW hTk, fun z => by
      show Tk (PW z) = _
      rw [hPWEq z]
      exact hTkEq _ _⟩
  obtain ⟨DW, hDW, hDWEq⟩ : ∃ DW : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) DW) ∧
      ∀ z : List Bool, DW z = (Wit z).drop (Mk z).length :=
    ⟨fun z => Dr (PW z), comp_poly hPW hDr, fun z => by
      show Dr (PW z) = _
      rw [hPWEq z]
      exact hDrEq _ _⟩
  -- the head of a list replaced by true: take the length of the tail with true in front
  obtain ⟨PT, hPT, hPTEq⟩ := pair_poly hCs hTl
  obtain ⟨CC, hCC, hCCEq⟩ : ∃ CC : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) CC) ∧
      ∀ z : List Bool, CC z = [true] ++ z.tail :=
    ⟨fun z => Cc (PT z), comp_poly hPT hCc, fun z => by
      show Cc (PT z) = _
      rw [hPTEq z, hCsEq z, hTlEq z]
      exact hCcEq _ _⟩
  obtain ⟨A2, hA2, hA2Eq⟩ := pair_poly hCC hId
  obtain ⟨HH, hHH, hHHEq⟩ : ∃ HH : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) HH) ∧
      ∀ z : List Bool, HH z = ([true] ++ z.tail).take z.length :=
    ⟨fun z => Tk (A2 z), comp_poly hA2 hTk, fun z => by
      show Tk (A2 z) = _
      rw [hA2Eq z, hCCEq z]
      exact hTkEq _ _⟩
  obtain ⟨HD, hHD, hHDEq⟩ : ∃ HD : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) HD) ∧
      ∀ z : List Bool, HD z = ([true] ++ (DW z).tail).take (DW z).length :=
    ⟨fun z => HH (DW z), comp_poly hDW hHH, fun z => hHHEq (DW z)⟩
  -- the new witness: the prefix, then the rest with its head replaced by true
  obtain ⟨U, hU, hUEq⟩ := MPP.Solutions.Pnp127.main TW HD hTW hHD
  obtain ⟨F, hF, hFEq⟩ := pair_poly hDec hU
  refine ⟨F, hF, fun x w => ?_⟩
  have hT : TW (pair x w) = w.take (x.count true) := by
    rw [hTWEq, hWitEq, hMkEq, hDecEq, List.length_replicate]
  have hD : DW (pair x w) = w.drop (x.count true) := by
    rw [hDWEq, hWitEq, hMkEq, hDecEq, List.length_replicate]
  have hH : HD (pair x w) = ([true] ++ (w.drop (x.count true)).tail).take (w.drop (x.count true)).length := by
    rw [hHDEq, hD]
  rw [hFEq, hDecEq, hUEq, hT, hH, List.singleton_append, set_eq_take_append]

end MPP.Solutions.Pnp225
