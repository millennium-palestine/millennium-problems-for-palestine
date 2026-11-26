import Mathlib

namespace MPP.Solutions.Pnp203

theorem main : ∀ q : List (Bool × Bool),
  (∃ j, j ≤ q.length ∧
    ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum = -1) →
  ∃ (p s : List (Bool × Bool)) (c : Bool × Bool), q = p ++ c :: s ∧ c = (true, true) ∧
    (p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
    ∀ j, j ≤ p.length →
      0 ≤ ((p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum := by
  intro q hq
  classical
  obtain ⟨J, hJle, hJval, hJmin⟩ : ∃ J, J ≤ q.length ∧
      ((q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take J).sum = -1 ∧ ∀ i, i < J → ((q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take i).sum ≠ -1 :=
    ⟨Nat.find hq, (Nat.find_spec hq).1, (Nat.find_spec hq).2, fun i hi h =>
      Nat.find_min hq hi ⟨le_of_lt (lt_of_lt_of_le hi (Nat.find_spec hq).1), h⟩⟩
  have hF : ∀ r : Bool × Bool, (-1 : ℤ) ≤ (if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) := by
    intro r
    split_ifs <;> norm_num
  have hcpair : ∀ c : Bool × Bool, (if c.1 && c.2 then (-1 : ℤ) else if c.1 then 0 else 1) = -1 → c = (true, true) := by
    rintro ⟨a, b⟩ h
    cases a <;> cases b <;> simp_all
  have hstep : ∀ (i : ℕ) (hi : i < q.length), ((q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take (i + 1)).sum =
      ((q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take i).sum + (if q[i].1 && q[i].2 then (-1 : ℤ) else if q[i].1 then 0 else 1) := by
    intro i hi
    rw [List.sum_take_succ _ _ (by simpa using hi)]
    simp only [List.getElem_map]
  have hN : ∀ i, i < J → 0 ≤ ((q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take i).sum := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hiq : i < q.length := by omega
      have h1 := ih (by omega)
      have h2 := hJmin (i + 1) hi
      have h3 := hstep i hiq
      have h4 := hF q[i]
      omega
  have hJ0 : J ≠ 0 := by
    rintro rfl
    simp at hJval
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  have hnq : n < q.length := by omega
  have hTn := hN n (by omega)
  have hsn := hstep n hnq
  have hval : (if q[n].1 && q[n].2 then (-1 : ℤ) else if q[n].1 then 0 else 1) = -1 := by
    have h4 := hF q[n]
    omega
  have hT0 : ((q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take n).sum = 0 := by
    have h4 := hF q[n]
    omega
  refine ⟨q.take n, q.drop (n + 1), q[n], ?_, hcpair _ hval, ?_, ?_⟩
  · rw [List.getElem_cons_drop, List.take_append_drop]
  · rw [List.map_take]
    exact hT0
  · intro j hj
    rw [List.length_take] at hj
    rw [List.map_take, List.take_take]
    exact hN _ (by omega)

end MPP.Solutions.Pnp203
