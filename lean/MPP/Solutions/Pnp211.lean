import Mathlib
import MPP.Solutions.Pnp193
import MPP.Solutions.Pnp196

namespace MPP.Solutions.Pnp211

theorem main : ∀ q : List (Bool × Bool), 0 < q.length →
  (∀ j, j ≤ q.length → 0 ≤ ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
  (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
  q = [(true, false)] ∨
  (∃ (a c : Bool × Bool) (mid : List (Bool × Bool)), q = a :: (mid ++ [c]) ∧ a.1 = false ∧ c = (true, true) ∧
    (mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
    ∀ j, j ≤ mid.length → 0 ≤ ((mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∨
  (∃ p s : List (Bool × Bool), q = p ++ s ∧ 0 < p.length ∧ 0 < s.length ∧
    (∀ j, j ≤ p.length → 0 ≤ ((p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∧
    (p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
    (∀ j, j ≤ s.length → 0 ≤ ((s.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∧
    (s.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0) := by
  intro q hpos hnn hsum
  obtain ⟨m, hm0, hmle, hmsum, hfirst, hrest, hdsum⟩ :=
    MPP.Solutions.Pnp193.main (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)
      (by rw [List.length_map]; exact hpos) (by rw [List.length_map]; exact hnn) hsum
  simp only [List.length_map] at hmle hrest
  -- take and drop commute with the height map
  have hT : ∀ n, (q.take n).map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)
      = (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take n :=
    fun n => by rw [List.map_take]
  have hD : ∀ n, ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).drop n)
      = (q.drop n).map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) :=
    fun n => by rw [List.map_drop]
  by_cases hlt : m < q.length
  · right; right
    refine ⟨q.take m, q.drop m, (List.take_append_drop m q).symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_take]; omega
    · rw [List.length_drop]; omega
    · intro j hj
      rw [List.length_take] at hj
      rw [hT m, List.take_take, Nat.min_eq_left (show j ≤ m by omega)]
      exact hnn j (by omega)
    · rw [hT m]; exact hmsum
    · intro j hj
      rw [List.length_drop] at hj
      rw [← hD m]
      exact hrest j hj
    · rw [← hD m]; exact hdsum
  · have hmq : m = q.length := by omega
    subst hmq
    rcases Nat.lt_or_ge q.length 2 with h2 | h2
    · rcases q with _ | ⟨r, _ | ⟨x, xs⟩⟩
      · simp at hpos
      · left
        obtain ⟨x, y⟩ := r
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
        cases x <;> cases y <;> simp_all
      · simp only [List.length_cons] at h2; omega
    · right; left
      have hfirst' : ∀ j, 0 < j → j < q.length → 0 < ((q.take j).map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum := by
        intro j hj0 hjl
        rw [hT j]
        exact hfirst j hj0 hjl
      obtain ⟨a, c, mid, hq, hA, hC, hM, hmid⟩ := MPP.Solutions.Pnp196.main q h2 hsum hfirst'
      refine ⟨a, c, mid, hq, ?_, ?_, hM, hmid⟩
      · obtain ⟨x, y⟩ := a
        cases x <;> cases y <;> simp_all
      · obtain ⟨x, y⟩ := c
        cases x <;> cases y <;> simp_all

end MPP.Solutions.Pnp211
