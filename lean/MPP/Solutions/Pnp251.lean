import Mathlib

namespace MPP.Solutions.Pnp251

theorem main : ∀ (H : Bool × Bool → ℤ), (∀ b : Bool, H (false, b) = 1) → H (true, true) = -1 →
    ∀ (a c : Bool × Bool) (mid : List (Bool × Bool)), a.1 = false → c = (true, true) →
    (mid.map H).sum = 0 → (∀ j, j ≤ mid.length → 0 ≤ ((mid.map H).take j).sum) →
    ((a :: (mid ++ [c])).map H).sum = 0 ∧
      ∀ j, j ≤ (a :: (mid ++ [c])).length → 0 ≤ (((a :: (mid ++ [c])).map H).take j).sum := by
  intro H hH1 hH2 a c mid ha hc hsum hpre
  subst hc
  have hA : H a = 1 := by
    obtain ⟨x, y⟩ := a
    simp only at ha
    subst ha
    exact hH1 y
  have hmap : (a :: (mid ++ [((true, true) : Bool × Bool)])).map H = 1 :: ((mid.map H) ++ [-1]) := by
    simp [hA, hH2]
  rw [hmap]
  constructor
  · simp [hsum]
  · intro j hj
    have hlen : (a :: (mid ++ [((true, true) : Bool × Bool)])).length = mid.length + 2 := by
      simp only [List.length_cons, List.length_append, List.length_nil]
    rw [hlen] at hj
    rcases j with _ | k
    · simp
    · rw [List.take_succ_cons, List.sum_cons]
      rcases Nat.lt_or_ge k (mid.length + 1) with hk | hk
      · have hk2 : k ≤ (mid.map H).length := by simp; omega
        rw [List.take_append_of_le_length hk2]
        have := hpre k (by omega)
        omega
      · have hk' : k = mid.length + 1 := by omega
        subst hk'
        rw [List.take_of_length_le (by simp)]
        simp [hsum]

end MPP.Solutions.Pnp251
