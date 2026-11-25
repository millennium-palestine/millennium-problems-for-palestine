import Mathlib

namespace MPP.Solutions.Pnp196

/-- The height step of a pair: -1 for a NAND pair, 0 for a no-op, +1 for a leaf or a copy. -/
def stepZ (r : Bool × Bool) : ℤ := if r.1 && r.2 then -1 else if r.1 then 0 else 1

theorem stepZ_cases (r : Bool × Bool) : stepZ r = 1 ∨ stepZ r = 0 ∨ stepZ r = -1 := by
  obtain ⟨x, y⟩ := r
  cases x <;> cases y <;> simp [stepZ]

theorem main : ∀ q : List (Bool × Bool), 2 ≤ q.length →
    (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    (∀ j, 0 < j → j < q.length →
      0 < ((q.take j).map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum) →
    ∃ (a c : Bool × Bool) (mid : List (Bool × Bool)), q = a :: (mid ++ [c]) ∧
      (if a.1 && a.2 then (-1 : ℤ) else if a.1 then 0 else 1) = 1 ∧
      (if c.1 && c.2 then (-1 : ℤ) else if c.1 then 0 else 1) = -1 ∧
      (mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
      ∀ j, j ≤ mid.length →
        0 ≤ ((mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum := by
  intro q hlen hsum hpos
  change (q.map stepZ).sum = 0 at hsum
  change ∀ j, 0 < j → j < q.length → 0 < ((q.take j).map stepZ).sum at hpos
  obtain ⟨a, r, rfl⟩ : ∃ a r, q = a :: r := by
    cases q with
    | nil => simp at hlen
    | cons a r => exact ⟨a, r, rfl⟩
  have hr : r ≠ [] := by
    rintro rfl
    simp at hlen
  obtain ⟨mid, c, rfl⟩ : ∃ mid c, r = mid ++ [c] := by
    rcases List.eq_nil_or_concat r with h | ⟨L, c, h⟩
    · exact absurd h hr
    · exact ⟨L, c, by rw [h, List.concat_eq_append]⟩
  have h1 : 0 < stepZ a := by
    have := hpos 1 (by norm_num) (by simp <;> omega)
    simpa using this
  have h2 : 0 < stepZ a + (mid.map stepZ).sum := by
    have := hpos (mid.length + 1) (by omega) (by simp <;> omega)
    have e : (a :: (mid ++ [c])).take (mid.length + 1) = a :: mid := by simp
    rw [e] at this
    simpa using this
  have hs : stepZ a + (mid.map stepZ).sum + stepZ c = 0 := by
    have := hsum
    simp [List.map_append] at this
    linarith
  have ka := stepZ_cases a
  have kc := stepZ_cases c
  have hA : stepZ a = 1 := by omega
  have hC : stepZ c = -1 := by omega
  have hM : (mid.map stepZ).sum = 0 := by omega
  refine ⟨a, c, mid, rfl, hA, hC, hM, fun j hj => ?_⟩
  have h3 := hpos (j + 1) (by omega) (by simp <;> omega)
  have e3 : (a :: (mid ++ [c])).take (j + 1) = a :: mid.take j := by
    simp [List.take_append_of_le_length hj]
  rw [e3] at h3
  simp only [List.map_cons, List.sum_cons] at h3
  show 0 ≤ ((mid.map stepZ).take j).sum
  rw [← List.map_take]
  omega

end MPP.Solutions.Pnp196
