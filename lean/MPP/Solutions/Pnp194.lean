import Mathlib
import MPP.Solutions.Pnp193

namespace MPP.Solutions.Pnp194

theorem main : ∀ d : List ℤ, (∀ j ≤ d.length, 0 ≤ (d.take j).sum) → d.sum = 0 →
    ∃ bs : List (List ℤ), d = bs.flatten ∧
      ∀ b ∈ bs, 0 < b.length ∧ b.sum = 0 ∧ (∀ j, 0 < j → j < b.length → 0 < (b.take j).sum) := by
  suffices H : ∀ n, ∀ d : List ℤ, d.length ≤ n → (∀ j ≤ d.length, 0 ≤ (d.take j).sum) → d.sum = 0 →
      ∃ bs : List (List ℤ), d = bs.flatten ∧
        ∀ b ∈ bs, 0 < b.length ∧ b.sum = 0 ∧ (∀ j, 0 < j → j < b.length → 0 < (b.take j).sum) from
    fun d => H d.length d le_rfl
  intro n
  induction n with
  | zero =>
    intro d hd _ _
    have hd0 : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp [hd0], by simp⟩
  | succ n ih =>
    intro d hd hnn hsum
    rcases Nat.eq_zero_or_pos d.length with h0 | hpos
    · have hd0 : d = [] := List.eq_nil_of_length_eq_zero h0
      exact ⟨[], by simp [hd0], by simp⟩
    · obtain ⟨m, hm0, hmlen, hmz, hfirst, hrest, hdrop⟩ :=
        MPP.Solutions.Pnp193.main d hpos hnn hsum
      have hlen : (d.drop m).length ≤ n := by
        rw [List.length_drop]
        omega
      have hrest' : ∀ j ≤ (d.drop m).length, 0 ≤ ((d.drop m).take j).sum := by
        rw [List.length_drop]
        exact hrest
      obtain ⟨bs, hbs, hprop⟩ := ih (d.drop m) hlen hrest' hdrop
      refine ⟨d.take m :: bs, ?_, ?_⟩
      · rw [List.flatten_cons, ← hbs, List.take_append_drop]
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · refine ⟨by rw [List.length_take]; omega, hmz, fun j hj1 hj2 => ?_⟩
          rw [List.length_take] at hj2
          rw [List.take_take, min_eq_left (by omega)]
          exact hfirst j hj1 (by omega)
        · exact hprop b hb'

end MPP.Solutions.Pnp194
