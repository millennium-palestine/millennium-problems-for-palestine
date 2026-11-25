import Mathlib

namespace MPP.Solutions.Bsd226

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] (b c d : A),
    (∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) →
    (∀ m : ℤ, normEDS b c d (m + 2) * normEDS b c d (m - 2) - b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
        + c * normEDS b c d m ^ 2 = 0) →
    ∀ m : ℤ,
      normEDS b c d 4 * (normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m - 1))
        + b ^ 3 * (normEDS b c d m * normEDS b c d (m - 2) * normEDS b c d (m + 2))
        - b * c * (normEDS b c d (m - 1) ^ 2 * normEDS b c d (m + 2)
          + normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2) = 0 := by
  intro A _ _ b c d hnv hR2
  obtain ⟨B, hB⟩ : ∃ B : ℤ → A, ∀ m : ℤ, B m =
      normEDS b c d 4 * (normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m - 1))
        + b ^ 3 * (normEDS b c d m * normEDS b c d (m - 2) * normEDS b c d (m + 2))
        - b * c * (normEDS b c d (m - 1) ^ 2 * normEDS b c d (m + 2)
          + normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2) := ⟨_, fun m => rfl⟩
  suffices h : ∀ m : ℤ, B m = 0 by
    intro m
    rw [← hB m]
    exact h m
  -- telescoping (bsd-224 inlined): Y(m) B(m+1) = Y(m+1) B(m)
  have tele : ∀ m : ℤ, normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m - 1) * B (m + 1)
      = normEDS b c d (m + 1) * normEDS b c d (m + 2) * normEDS b c d m * B m := by
    intro m
    have h1 := hR2 m
    have h2 := hR2 (m + 1)
    rw [show m + 1 + 2 = m + 3 by ring, show m + 1 - 2 = m - 1 by ring,
      show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring] at h2
    rw [hB, hB]
    rw [show m + 1 + 2 = m + 3 by ring, show m + 1 - 2 = m - 1 by ring,
      show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring]
    linear_combination (b * normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m + 2)
        * normEDS b c d (m - 2)) * h2
      - (b * normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m + 3) * normEDS b c d (m - 1)) * h1
  have hB2 : B 2 = 0 := by
    rw [hB]
    norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four] <;> ring
  have hB0 : B 0 = 0 := by
    rw [hB]
    norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four, normEDS_neg] <;> ring
  have hB1 : B 1 = 0 := by
    rw [hB]
    norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four, normEDS_neg] <;> ring
  -- the bracket is odd: B(-k) = -B(k)
  have hodd : ∀ k : ℤ, B (-k) = -B k := by
    intro k
    rw [hB, hB]
    rw [show -k + 1 = -(k - 1) by ring, show -k - 1 = -(k + 1) by ring,
      show -k - 2 = -(k + 2) by ring, show -k + 2 = -(k - 2) by ring]
    simp only [normEDS_neg]
    ring
  -- for n ≥ 0 the bracket vanishes at n + 2, by induction with the telescoping identity
  have hpos : ∀ n : ℕ, B ((n : ℤ) + 2) = 0 := by
    intro n
    induction n with
    | zero => simpa using hB2
    | succ n ih =>
      have e : ((n + 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 2 + 1 := by push_cast; ring
      rw [e]
      have hY : normEDS b c d ((n : ℤ) + 2) * normEDS b c d ((n : ℤ) + 2 + 1)
          * normEDS b c d ((n : ℤ) + 2 - 1) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))) (hnv _ (by omega))
      have h := tele ((n : ℤ) + 2)
      rw [ih, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hY
  intro m
  rcases le_or_gt 2 m with hm | hm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 2 := ⟨(m - 2).toNat, by omega⟩
    exact hpos n
  · have hneg : B (-m) = 0 := by
      rcases le_or_gt 2 (-m) with h2 | h2
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, -m = (n : ℤ) + 2 := ⟨(-m - 2).toNat, by omega⟩
        rw [hn]
        exact hpos n
      · rcases (show -m = -1 ∨ -m = 0 ∨ -m = 1 by omega) with h0 | h0 | h0
        · have := hodd 1
          rw [hB1, neg_zero] at this
          rw [h0]
          exact this
        · rw [h0]
          exact hB0
        · rw [h0]
          exact hB1
    have := hodd (-m)
    rw [neg_neg] at this
    rw [this, hneg, neg_zero]

end MPP.Solutions.Bsd226
