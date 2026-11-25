import Mathlib

namespace MPP.Solutions.Pnp189

theorem main : ∀ d : List ℤ, (∀ e ∈ d, -1 ≤ e ∧ e ≤ 1) → d.sum < 0 →
    ∃ k, k < d.length ∧ (d.take (k + 1)).sum = -1 ∧ ∀ j ≤ k, 0 ≤ (d.take j).sum := by
  intro d hd hneg
  have hex : ∃ m, (d.take m).sum < 0 := ⟨d.length, by simpa using hneg⟩
  have hm : (d.take (Nat.find hex)).sum < 0 := Nat.find_spec hex
  have hle : Nat.find hex ≤ d.length := Nat.find_min' hex (by simpa using hneg)
  have hmin : ∀ j, j < Nat.find hex → 0 ≤ (d.take j).sum := fun j hj =>
    not_lt.mp (Nat.find_min hex hj)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hm
    simp at hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hkl : k < d.length := by omega
  have hstep : (d.take (k + 1)).sum = (d.take k).sum + d[k] := by
    rw [List.sum_take_succ d k hkl]
  have hdk : -1 ≤ d[k] := (hd _ (List.getElem_mem hkl)).1
  have h1 : 0 ≤ (d.take k).sum := hmin k (by omega)
  rw [hk] at hm
  refine ⟨k, hkl, ?_, fun j hj => hmin j (by omega)⟩
  omega

end MPP.Solutions.Pnp189
