import Mathlib

namespace MPP.Solutions.Pnp295

theorem main : ∀ (H : Bool × Bool → ℤ), (∀ r : Bool × Bool, H r = if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) →
    ∀ (m : ℕ) (q : List (Bool × Bool)), (∀ j, j ≤ q.length → 0 ≤ ((q.map H).take j).sum) → (q.map H).sum = (m : ℤ) →
    ∃ (bs : List (List (Bool × Bool))) (us : List (Bool × Bool)) (last : List (Bool × Bool)),
      bs.length = m ∧ us.length = m ∧ (∀ u ∈ us, H u = 1) ∧
      (∀ b ∈ bs ++ [last], (∀ j, j ≤ b.length → 0 ≤ ((b.map H).take j).sum) ∧ (b.map H).sum = 0) ∧
      q = (List.zipWith (fun b u => b ++ [u]) bs us).flatten ++ last := by
  intro H hH
  have hle : ∀ r, H r ≤ 1 := by
    intro r
    rw [hH r]
    split_ifs <;> norm_num
  -- the last zero of the prefix sums splits off one up pair
  have split : ∀ q : List (Bool × Bool), (∀ j, j ≤ q.length → 0 ≤ ((q.map H).take j).sum) →
      0 < (q.map H).sum →
      ∃ (p : List (Bool × Bool)) (r : Bool × Bool) (s : List (Bool × Bool)), q = p ++ r :: s ∧ H r = 1 ∧
        (p.map H).sum = 0 ∧ (∀ j, j ≤ p.length → 0 ≤ ((p.map H).take j).sum) ∧
        (s.map H).sum = (q.map H).sum - 1 ∧ (∀ j, j ≤ s.length → 0 ≤ ((s.map H).take j).sum) := by
    intro q hnn hpos
    have hP0 : ((q.map H).take 0).sum = 0 := by simp
    have hkspec0 := Nat.findGreatest_spec (P := fun j => ((q.map H).take j).sum = 0) (Nat.zero_le q.length) hP0
    set k := Nat.findGreatest (fun j => ((q.map H).take j).sum = 0) q.length with hk
    have hkspec : ((q.map H).take k).sum = 0 := hkspec0
    have hkle : k ≤ q.length := Nat.findGreatest_le _
    have hmax : ∀ j, k < j → j ≤ q.length → ((q.map H).take j).sum ≠ 0 :=
      fun j hj hjn => Nat.findGreatest_is_greatest hj hjn
    have hkn : k < q.length := by
      by_contra hcon
      have hkeq : k = q.length := le_antisymm hkle (not_lt.mp hcon)
      have h0 : ((q.map H).take q.length).sum = 0 := hkeq ▸ hkspec
      have hlw : (q.map H).length = q.length := by simp
      rw [← hlw, List.take_length] at h0
      omega
    have hone : ∀ j, k < j → j ≤ q.length → 1 ≤ ((q.map H).take j).sum := by
      intro j hj hjn
      have h1 := hmax j hj hjn
      have h2 := hnn j hjn
      omega
    have hsplit : q = q.take k ++ q[k] :: q.drop (k + 1) := by
      have h := (List.take_append_drop k q).symm
      rw [List.drop_eq_getElem_cons hkn] at h
      exact h
    have hWk : ((q.map H).take (k + 1)).sum = ((q.map H).take k).sum + H q[k] := by
      rw [List.sum_take_succ _ _ (by simpa using hkn)]
      simp
    have hHr : H q[k] = 1 := by
      have h1 := hone (k + 1) (Nat.lt_succ_self k) (Nat.succ_le_of_lt hkn)
      have h2 := hle q[k]
      omega
    have hmapTake : (q.take k).map H = (q.map H).take k := by
      simp [List.map_take]
    have hd : (q.drop (k + 1)).map H = (q.map H).drop (k + 1) := by
      simp [List.map_drop]
    have hlen : (q.drop (k + 1)).length = q.length - (k + 1) := by
      simp
    refine ⟨q.take k, q[k], q.drop (k + 1), hsplit, hHr, ?_, ?_, ?_, ?_⟩
    · rw [hmapTake]
      exact hkspec
    · intro j hj
      have hjk : j ≤ k := le_trans hj (by simp)
      have hjn : j ≤ q.length := by omega
      rw [hmapTake, List.take_take, Nat.min_eq_left hjk]
      exact hnn j hjn
    · have hs := List.sum_take_add_sum_drop (q.map H) (k + 1)
      rw [hd]
      omega
    · intro j hj
      have hjn : k + 1 + j ≤ q.length := by omega
      have hsum : ((q.map H).take (k + 1 + j)).sum =
          ((q.map H).take (k + 1)).sum + (((q.map H).drop (k + 1)).take j).sum := by
        rw [List.take_add, List.sum_append]
      have h1 := hone (k + 1 + j) (by omega) hjn
      rw [hd]
      omega
  have peel : ∀ (m : ℕ) (q : List (Bool × Bool)), (∀ j, j ≤ q.length → 0 ≤ ((q.map H).take j).sum) →
      (q.map H).sum = (m : ℤ) →
      ∃ (bs : List (List (Bool × Bool))) (us : List (Bool × Bool)) (last : List (Bool × Bool)),
        bs.length = m ∧ us.length = m ∧ (∀ u ∈ us, H u = 1) ∧
        (∀ b ∈ bs ++ [last], (∀ j, j ≤ b.length → 0 ≤ ((b.map H).take j).sum) ∧ (b.map H).sum = 0) ∧
        q = (List.zipWith (fun b u => b ++ [u]) bs us).flatten ++ last := by
    intro m
    induction m with
    | zero =>
      intro q hnn hsum
      refine ⟨[], [], q, rfl, rfl, by simp, ?_, by simp⟩
      intro b hb
      rw [List.nil_append, List.mem_singleton] at hb
      rw [hb]
      exact ⟨hnn, by simpa using hsum⟩
    | succ m ih =>
      intro q hnn hsum
      have hpos : 0 < (q.map H).sum := by
        rw [hsum]
        positivity
      obtain ⟨p, r, s, hq, hr, hp0, hpnn, hs, hsnn⟩ := split q hnn hpos
      obtain ⟨bs, us, last, hl1, hl2, hu, hb, heq⟩ :=
        ih s hsnn (by rw [hs, hsum]; push_cast; ring)
      refine ⟨p :: bs, r :: us, last, by simp [hl1], by simp [hl2], ?_, ?_, ?_⟩
      · intro u hu'
        rcases List.mem_cons.mp hu' with h | h
        · rw [h]
          exact hr
        · exact hu u h
      · intro b hb'
        rw [List.cons_append, List.mem_cons] at hb'
        rcases hb' with h | h
        · rw [h]
          exact ⟨hpnn, hp0⟩
        · exact hb b h
      · rw [hq, heq]
        simp [List.zipWith_cons_cons, List.flatten_cons, List.append_assoc]
  intro m q hnn hsum
  exact peel m q hnn hsum

end MPP.Solutions.Pnp295
