import Mathlib

namespace MPP.Solutions.Pnp344

-- pnp-343 content: the Boolean reachable-set fold decides an existential chain of relations
theorem chain343 : ∀ (n : ℕ) (R : ℕ → Bool → Bool → Bool) (v t : Bool),
    ((∃ s : ℕ → Bool, s 0 = v ∧ s n = t ∧ ∀ k, k < n → R k (s k) (s (k + 1)) = true) ↔
      ((t = true ∧ ((List.range n).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
          (!v, v)).2 = true) ∨
       (t = false ∧ ((List.range n).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
          (!v, v)).1 = true))) := by
  intro n R v
  have key : ∀ m : ℕ, ∀ y : Bool, ((∃ s : ℕ → Bool, s 0 = v ∧ s m = y ∧ ∀ k, k < m → R k (s k) (s (k + 1)) = true) ↔
      ((y = true ∧ ((List.range m).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
          (!v, v)).2 = true) ∨
       (y = false ∧ ((List.range m).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
          (!v, v)).1 = true))) := by
    intro m
    induction m with
    | zero =>
      intro y
      constructor
      · rintro ⟨s, h0, hy, -⟩
        have hvy : v = y := by rw [← h0, hy]
        subst hvy
        cases v <;> simp
      · intro h
        refine ⟨fun _ => v, rfl, ?_, by simp⟩
        rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
        · simpa using h
        · simpa using h
    | succ m ih =>
      intro y
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      constructor
      · rintro ⟨s, h0, hy, hs⟩
        have hx := (ih (s m)).1 ⟨s, h0, rfl, fun k hk => hs k (by omega)⟩
        have hr := hs m (by omega)
        rw [hy] at hr
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hr <;> cases y <;> simp_all
      · intro h
        obtain ⟨x, hx1, hx2⟩ : ∃ x : Bool, ((x = true ∧ ((List.range m).foldl (fun (S : Bool × Bool) (k : ℕ) =>
            ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
            (!v, v)).2 = true) ∨ (x = false ∧ ((List.range m).foldl (fun (S : Bool × Bool) (k : ℕ) =>
            ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
            (!v, v)).1 = true)) ∧ R m x y = true := by
          rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp only [Bool.or_eq_true, Bool.and_eq_true] at h <;>
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨false, Or.inr ⟨rfl, h1⟩, h2⟩
          · exact ⟨true, Or.inl ⟨rfl, h1⟩, h2⟩
          · exact ⟨false, Or.inr ⟨rfl, h1⟩, h2⟩
          · exact ⟨true, Or.inl ⟨rfl, h1⟩, h2⟩
        obtain ⟨s, h0, hsm, hs⟩ := (ih x).2 hx1
        refine ⟨fun k => if k = m + 1 then y else s k, ?_, ?_, ?_⟩
        · simp [h0]
        · simp
        · intro k hk
          by_cases hkm : k = m
          · subst hkm
            simp [hsm, hx2]
          · have h1 : k ≠ m + 1 := by omega
            have h2 : k + 1 ≠ m + 1 := by omega
            simp only [h1, h2, if_false]
            exact hs k (by omega)
  exact fun t => key n t

-- pnp-344: a chain of block-boundary relations X, with the table c agreeing with X on
-- every interval, is decided by the Boolean reachable-set fold over the table entries
theorem main : ∀ (p : ℕ → ℕ) (X : ℕ → ℕ → Bool × Bool → Prop) (c : ℕ → ℕ → Bool × Bool → Bool),
    (∀ k, p k ≤ p (k + 1)) →
    (∀ i j : ℕ, ∀ r : Bool × Bool, i ≤ j → (c i j r = true ↔ X i j r)) →
    ∀ (n : ℕ) (v t : Bool),
    ((∃ s : ℕ → Bool, s 0 = v ∧ s n = t ∧ ∀ k, k < n → X (p k) (p (k + 1)) (s k, s (k + 1))) ↔
      ((t = true ∧ ((List.range n).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && c (p k) (p (k + 1)) (false, false)) || (S.2 && c (p k) (p (k + 1)) (true, false)),
           (S.1 && c (p k) (p (k + 1)) (false, true)) || (S.2 && c (p k) (p (k + 1)) (true, true))))
          (!v, v)).2 = true) ∨
       (t = false ∧ ((List.range n).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && c (p k) (p (k + 1)) (false, false)) || (S.2 && c (p k) (p (k + 1)) (true, false)),
           (S.1 && c (p k) (p (k + 1)) (false, true)) || (S.2 && c (p k) (p (k + 1)) (true, true))))
          (!v, v)).1 = true))) := by
  intro p X c hp hc n v t
  have h1 : (∃ s : ℕ → Bool, s 0 = v ∧ s n = t ∧ ∀ k, k < n → X (p k) (p (k + 1)) (s k, s (k + 1))) ↔
      (∃ s : ℕ → Bool, s 0 = v ∧ s n = t ∧ ∀ k, k < n → c (p k) (p (k + 1)) (s k, s (k + 1)) = true) := by
    constructor
    · rintro ⟨s, h0, hn, h⟩
      exact ⟨s, h0, hn, fun k hk => (hc _ _ _ (hp k)).2 (h k hk)⟩
    · rintro ⟨s, h0, hn, h⟩
      exact ⟨s, h0, hn, fun k hk => (hc _ _ _ (hp k)).1 (h k hk)⟩
  exact h1.trans (chain343 n (fun k x y => c (p k) (p (k + 1)) (x, y)) v t)

end MPP.Solutions.Pnp344
