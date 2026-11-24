import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp071

open MPP.PvsNP Turing

/-- A common prefix does not change the lexicographic order of the rest. -/
theorem append_lt_iff (u a b : List Bool) : u ++ a < u ++ b ↔ a < b := by
  induction u with
  | nil => simp
  | cons x u ih => simpa using ih

/-- A list starting with `true` is not below a list starting with `false`. -/
theorem not_lt_true_false (a b : List Bool) : ¬ (true :: a < false :: b) := by
  intro h
  rw [List.cons_lt_cons_iff] at h
  rcases h with h | ⟨h, _⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem main : ∀ (A : List Bool → Prop) (N : ℕ) (E : List Bool → Bool) (step : List Bool → List Bool),
    (∀ u : List Bool, E u = true ↔
      ∃ w : List Bool, w.length = N ∧ (∃ t : List Bool, w = u ++ t) ∧ A w) →
    (∀ u : List Bool, step u = if E (u ++ [false]) = true then u ++ [false] else u ++ [true]) →
    ∀ w : List Bool, w.length = N → A w → ¬ (w < step^[N] []) := by
  intro A N E step hE hstep
  have hlen : ∀ u : List Bool, (step u).length = u.length + 1 := by
    intro u
    rw [hstep u]
    split <;> simp
  have hpre : ∀ u : List Bool, u <+: step u := by
    intro u
    rw [hstep u]
    split
    · exact List.prefix_append u [false]
    · exact List.prefix_append u [true]
  have hiter : ∀ (m : ℕ) (u : List Bool), u <+: step^[m] u := by
    intro m
    induction m with
    | zero => intro u; exact List.prefix_refl u
    | succ m ih =>
      intro u
      rw [Function.iterate_succ_apply]
      exact (hpre u).trans (ih (step u))
  -- the greedy step keeps a witness alive, as long as the prefix is shorter than N
  have hext : ∀ u : List Bool, u.length < N → E u = true → E (step u) = true := by
    intro u hlt hu
    obtain ⟨w, hw, ⟨t, rfl⟩, hA⟩ := (hE u).1 hu
    rw [hstep u]
    by_cases hf : E (u ++ [false]) = true
    · rw [if_pos hf]
      exact hf
    · rw [if_neg hf]
      obtain ⟨c, t', rfl⟩ : ∃ c t', t = c :: t' := by
        cases t with
        | nil => simp at hw; omega
        | cons c t' => exact ⟨c, t', rfl⟩
      cases c
      · exact absurd ((hE (u ++ [false])).2 ⟨u ++ [false] ++ t', by simpa using hw, ⟨t', rfl⟩,
          by simpa using hA⟩) hf
      · exact (hE (u ++ [true])).2 ⟨u ++ [true] ++ t', by simpa using hw, ⟨t', rfl⟩,
          by simpa using hA⟩
  -- the invariant: from a prefix u that the greedy has reached, no accepted witness is below
  have claim : ∀ m : ℕ, ∀ u : List Bool, u.length + m = N → E u = true →
      ∀ w : List Bool, w.length = N → A w → u <+: w → ¬ (w < step^[m] u) := by
    intro m
    induction m with
    | zero =>
      intro u hu _ w hw _ hpre' habs
      simp only [Function.iterate_zero, id] at habs
      have h := hpre'.eq_of_length (by omega)
      subst h
      exact lt_irrefl _ habs
    | succ m ih =>
      intro u hu hEu w hw hA hpre' habs
      rw [Function.iterate_succ_apply] at habs
      have hlt : u.length < N := by omega
      have hEu' : E (step u) = true := hext u hlt hEu
      obtain ⟨v, rfl⟩ := hpre'
      have hne : v ≠ [] := by
        intro h
        subst h
        simp only [List.append_nil] at hw
        omega
      obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      cases c with
      | false =>
        have hEf : E (u ++ [false]) = true :=
          (hE (u ++ [false])).2 ⟨u ++ false :: rest, hw, ⟨rest, by simp⟩, hA⟩
        have hs : step u = u ++ [false] := by rw [hstep u, if_pos hEf]
        rw [hs] at habs
        exact ih (u ++ [false]) (by simp only [List.length_append, List.length_singleton]; omega)
          hEf _ hw hA ⟨rest, by simp⟩ habs
      | true =>
        by_cases hf : E (u ++ [false]) = true
        · have hs : step u = u ++ [false] := by rw [hstep u, if_pos hf]
          rw [hs] at habs
          obtain ⟨r, hr⟩ := hiter m (u ++ [false])
          rw [← hr] at habs
          have h2 := (append_lt_iff u (true :: rest) (false :: r)).1 (by simpa using habs)
          exact not_lt_true_false rest r h2
        · have hs : step u = u ++ [true] := by rw [hstep u, if_neg hf]
          have hEt : E (u ++ [true]) = true := by rw [← hs]; exact hEu'
          rw [hs] at habs
          exact ih (u ++ [true]) (by simp only [List.length_append, List.length_singleton]; omega)
            hEt _ hw hA ⟨rest, by simp⟩ habs
  intro w hw hA
  have hEnil : E [] = true := (hE []).2 ⟨w, hw, ⟨w, rfl⟩, hA⟩
  exact claim N [] (by simp) hEnil w hw hA (by simp)

end MPP.Solutions.Pnp071
