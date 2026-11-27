import Mathlib
import MPP.Solutions.Pnp203

namespace MPP.Solutions.Pnp263

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

theorem main : ∀ q : List (Bool × Bool), ∃ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
    q = (items.map fun b => b ++ [(true, true)]).flatten ++ T ∧
    (∀ b ∈ items,
      (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
      ∀ j, j ≤ b.length →
        0 ≤ ((b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∧
    ∀ j, j ≤ T.length →
      0 ≤ ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum := by
  classical
  suffices H : ∀ n : ℕ, ∀ q : List (Bool × Bool), q.length ≤ n → ∃ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
      q = (items.map fun b => b ++ [(true, true)]).flatten ++ T ∧
      (∀ b ∈ items,
        (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
        ∀ j, j ≤ b.length →
          0 ≤ ((b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∧
      ∀ j, j ≤ T.length →
        0 ≤ ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum from
    fun q => H q.length q le_rfl
  intro n
  induction n with
  | zero =>
    intro q hq
    have hnil : q = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨[], [], ?_, by simp, by simp⟩
    simp [hnil]
  | succ n ih =>
    intro q hq
    have hL : ∀ x ∈ q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1), -1 ≤ x := by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
      split_ifs <;> norm_num
    by_cases hneg : ∃ j, j ≤ q.length ∧
        ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum < 0
    · obtain ⟨j, hjlen, hjneg⟩ := hneg
      obtain ⟨J, hJ, hJval⟩ := dip_to_minus_one _ hL
        ⟨j, by simpa only [List.length_map] using hjlen, hjneg⟩
      obtain ⟨p, s, c, hq_eq, hc, hp_sum, hp_nonneg⟩ :=
        MPP.Solutions.Pnp203.main q ⟨J, by simpa only [List.length_map] using hJ, hJval⟩
      have hlen := congrArg List.length hq_eq
      simp only [List.length_append, List.length_cons] at hlen
      obtain ⟨items', T', hs_eq, hitems', hT'⟩ := ih s (by omega)
      refine ⟨p :: items', T', ?_, ?_, hT'⟩
      · rw [hq_eq, hs_eq, hc]
        simp [List.append_assoc]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact ⟨hp_sum, hp_nonneg⟩
        · exact hitems' b hb'
    · simp only [not_exists, not_and, not_lt] at hneg
      refine ⟨[], q, ?_, by simp, hneg⟩
      simp

end MPP.Solutions.Pnp263
