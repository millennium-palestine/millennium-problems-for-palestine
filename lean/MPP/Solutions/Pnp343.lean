import Mathlib

namespace MPP.Solutions.Pnp343

-- one more step of a chain: the chain of length m+1 to y is a chain of length m to some x with R m x y
theorem chain_succ (R : ℕ → Bool → Bool → Bool) (v : Bool) (m : ℕ) (y : Bool) :
    (∃ s : ℕ → Bool, s 0 = v ∧ s (m + 1) = y ∧ ∀ k, k < m + 1 → R k (s k) (s (k + 1)) = true) ↔
      ∃ x : Bool, (∃ s : ℕ → Bool, s 0 = v ∧ s m = x ∧ ∀ k, k < m → R k (s k) (s (k + 1)) = true) ∧
        R m x y = true := by
  constructor
  · rintro ⟨s, h0, hy, hs⟩
    refine ⟨s m, ⟨s, h0, rfl, fun k hk => hs k (by omega)⟩, ?_⟩
    have h := hs m (by omega)
    rw [hy] at h
    exact h
  · rintro ⟨x, ⟨s, h0, hx, hs⟩, hr⟩
    refine ⟨fun k => if k ≤ m then s k else y, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro k hk
      by_cases hkm : k < m
      · have h1 : k ≤ m := by omega
        have h2 : k + 1 ≤ m := by omega
        simp only [h1, h2, if_true]
        exact hs k hkm
      · have hkm' : k = m := by omega
        subst hkm'
        simp [hx, hr]

theorem reach_iff (R : ℕ → Bool → Bool → Bool) (v : Bool) : ∀ (m : ℕ) (y : Bool),
    ((∃ s : ℕ → Bool, s 0 = v ∧ s m = y ∧ ∀ k, k < m → R k (s k) (s (k + 1)) = true) ↔
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
      have hvy : v = y := h0.symm.trans hy
      subst hvy
      cases v <;> simp
    · intro h
      rcases h with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
      · refine ⟨fun _ => v, rfl, ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
        simpa using hv
      · refine ⟨fun _ => v, rfl, ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
        simpa using hv
  | succ m ih =>
    intro y
    rw [chain_succ R v m y]
    simp only [ih]
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Bool.exists_bool]
    cases y <;> simp [Bool.and_eq_true, Bool.or_eq_true]

theorem main : ∀ (n : ℕ) (R : ℕ → Bool → Bool → Bool) (v t : Bool),
    ((∃ s : ℕ → Bool, s 0 = v ∧ s n = t ∧ ∀ k, k < n → R k (s k) (s (k + 1)) = true) ↔
      ((t = true ∧ ((List.range n).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
          (!v, v)).2 = true) ∨
       (t = false ∧ ((List.range n).foldl (fun (S : Bool × Bool) (k : ℕ) =>
          ((S.1 && R k false false) || (S.2 && R k true false), (S.1 && R k false true) || (S.2 && R k true true)))
          (!v, v)).1 = true))) := by
  intro n R v t
  exact reach_iff R v n t

end MPP.Solutions.Pnp343
