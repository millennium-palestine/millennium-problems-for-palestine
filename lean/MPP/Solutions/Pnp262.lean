import Mathlib

namespace MPP.Solutions.Pnp262

theorem dip_to_minus_one (L : List ℤ) (hL : ∀ x ∈ L, -1 ≤ x)
    (h : ∃ j, j ≤ L.length ∧ (L.take j).sum < 0) :
    ∃ j, j ≤ L.length ∧ (L.take j).sum = -1 := by
  classical
  obtain ⟨hJle, hJneg⟩ := Nat.find_spec h
  have hJ0 : Nat.find h ≠ 0 := by
    intro h0
    rw [h0] at hJneg
    simp at hJneg
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
  have hJeq : Nat.find h = k + 1 := hk
  have hkmin := Nat.find_min h (show k < Nat.find h by omega)
  have hk_le : k ≤ L.length := by omega
  have hk_nonneg : 0 ≤ (L.take k).sum := not_lt.mp (not_and.mp hkmin hk_le)
  have hklt : k < L.length := by omega
  have hstep : (L.take (k + 1)).sum = (L.take k).sum + L[k] := List.sum_take_succ L k hklt
  have hLk : -1 ≤ L[k] := hL _ (List.getElem_mem hklt)
  have hneg : (L.take (Nat.find h)).sum < 0 := hJneg
  refine ⟨Nat.find h, hJle, ?_⟩
  rw [hJeq] at hneg ⊢
  omega

theorem main : ∀ q : List (Bool × Bool),
    (∃ j, j ≤ q.length ∧
      ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum < 0) →
    ∃ j, j ≤ q.length ∧
      ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum = -1 := by
  intro q hq
  have hL : ∀ x ∈ q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1), -1 ≤ x := by
    intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> norm_num
  obtain ⟨j, hj, hval⟩ := dip_to_minus_one _ hL (by
    obtain ⟨j, hj, hneg⟩ := hq
    exact ⟨j, by simpa only [List.length_map] using hj, hneg⟩)
  exact ⟨j, by simpa only [List.length_map] using hj, hval⟩

end MPP.Solutions.Pnp262
