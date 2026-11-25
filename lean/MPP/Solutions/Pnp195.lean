import Mathlib
import MPP.Solutions.Pnp194

namespace MPP.Solutions.Pnp195

/-- Cutting a pair list along the blocks of a list of integer lists. -/
theorem lift (f : Bool × Bool → ℤ) : ∀ (bs : List (List ℤ)) (ps : List (Bool × Bool)),
    ps.map f = bs.flatten → ∃ qs : List (List (Bool × Bool)), ps = qs.flatten ∧ qs.map (List.map f) = bs := by
  intro bs
  induction bs with
  | nil =>
    intro ps h
    have hps : ps = [] := by simpa using h
    exact ⟨[], by simp [hps], rfl⟩
  | cons b bs ih =>
    intro ps h
    rw [List.flatten_cons] at h
    obtain ⟨l₁, l₂, hps, h₁, h₂⟩ := List.append_eq_map_iff.mp h.symm
    obtain ⟨qs, hq, hqs⟩ := ih l₂ h₂
    exact ⟨l₁ :: qs, by simp [hps, hq], by simp [h₁, hqs]⟩

theorem main : ∀ ps : List (Bool × Bool),
    (∀ j ≤ ps.length, 0 ≤ ((ps.map fun q : Bool × Bool => if q.1 && q.2 then (-1 : ℤ) else if q.1 then 0 else 1).take j).sum) →
    (ps.map fun q : Bool × Bool => if q.1 && q.2 then (-1 : ℤ) else if q.1 then 0 else 1).sum = 0 →
    ∃ qs : List (List (Bool × Bool)), ps = qs.flatten ∧
      ∀ q ∈ qs, 0 < q.length ∧
        (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
        ∀ j, 0 < j → j < q.length →
          0 < ((q.take j).map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum := by
  intro ps hnn hsum
  obtain ⟨bs, hbs, hblk⟩ := MPP.Solutions.Pnp194.main _
    (fun j hj => hnn j (by simpa using hj)) hsum
  obtain ⟨qs, hq, hqs⟩ := lift _ bs ps hbs
  refine ⟨qs, hq, fun q hqm => ?_⟩
  have hmem : q.map (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) ∈ bs := by
    rw [← hqs]
    exact List.mem_map_of_mem hqm
  obtain ⟨h1, h2, h3⟩ := hblk _ hmem
  refine ⟨by simpa using h1, h2, fun j hj1 hj2 => ?_⟩
  have h4 := h3 j hj1 (by simpa using hj2)
  rw [← List.map_take] at h4
  exact h4

end MPP.Solutions.Pnp195
