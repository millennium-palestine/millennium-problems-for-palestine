import Mathlib

namespace MPP.Solutions.Pnp342

theorem main : ∀ (n : ℕ) (F : ℕ → Bool → Bool) (R : ℕ → Bool → Bool → Prop),
    (∀ k x y, R k x y ↔ F k x = y) → ∀ v t : Bool,
    ((∃ s : ℕ → Bool, s 0 = v ∧ s n = t ∧ ∀ k, k < n → R k (s k) (s (k + 1))) ↔
      (List.range n).foldl (fun acc k => F k acc) v = t) := by
  intro n F R hR v t
  constructor
  · rintro ⟨s, h0, hn, hs⟩
    -- the witness agrees with the fold of the first m steps, for every m ≤ n
    have hfold : ∀ m, m ≤ n → s m = (List.range m).foldl (fun acc k => F k acc) v := by
      intro m
      induction m with
      | zero => intro _; simpa using h0
      | succ m ih =>
        intro hm
        have h1 := (hR m (s m) (s (m + 1))).1 (hs m (by omega))
        rw [ih (by omega)] at h1
        simpa [List.range_succ, List.foldl_append] using h1.symm
    exact (hfold n le_rfl).symm.trans hn
  · intro h
    refine ⟨fun k => (List.range k).foldl (fun acc j => F j acc) v, rfl, h, ?_⟩
    intro k _
    rw [hR]
    simp [List.range_succ, List.foldl_append]

end MPP.Solutions.Pnp342
