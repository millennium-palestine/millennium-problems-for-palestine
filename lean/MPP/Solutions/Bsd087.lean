import Mathlib

namespace MPP.Solutions.Bsd087

theorem main : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) s := by
  intro s hs
  have h1 : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by simp) hs
  have h2 := h1.convolution h1
  convert h2 using 2
  rename_i n
  rw [LSeries.convolution_def]
  dsimp only
  rw [← Nat.map_div_right_divisors, Finset.sum_map]
  simp

end MPP.Solutions.Bsd087
