import Mathlib
import MPP.Solutions.Pnp316

namespace MPP.Solutions.Pnp321

theorem main : ∀ (n b t : ℕ) (G : Fin b → (Fin (3 * b) → Bool) → Bool) (p : List Bool), 0 < n → 0 < b → p.length ≤ n * b →
  ∃ D : List (List (ℕ × Bool)),
    (∀ a : ℕ → Bool, (((∀ k : Fin p.length, a k.val = p.getD k.val false) ∧
        ∀ s : Fin t, ∀ i : Fin n, ∀ j : Fin b,
          a (n * b * (s.val + 1) + i.val * b + j.val) =
            G j (fun w : Fin (3 * b) => a (n * b * s.val + ((i.val + w.val / b) % n) * b + w.val % b))) ∧
        a (n * b * t) = true) ↔
      ∀ d ∈ D, ∃ l ∈ d, a l.1 = l.2) ∧
    D.length ≤ 2 ^ (3 * b + 1) * (n * b * t) + p.length + 1 ∧
    ∀ d ∈ D, ∀ l ∈ d, l.1 < n * b * (t + 1) := by
  intro n b t G p hn hb hp
  obtain ⟨D0, hiff0, hlen0, hvar0⟩ := MPP.Solutions.Pnp316.main n b t G
  have hnb : 0 < n * b := Nat.mul_pos hn hb
  refine ⟨D0 ++ (List.finRange p.length).map (fun k => [(k.val, p.getD k.val false)]) ++ [[(n * b * t, true)]], ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨⟨h0, hloc⟩, hout⟩ d hd
      rcases List.mem_append.mp hd with hd1 | hd2
      · rcases List.mem_append.mp hd1 with hd3 | hd4
        · exact (hiff0 a).mp hloc d hd3
        · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd4
          exact ⟨(k.val, p.getD k.val false), List.mem_singleton_self _, h0 k⟩
      · simp only [List.mem_singleton] at hd2
        subst hd2
        exact ⟨(n * b * t, true), List.mem_singleton_self _, hout⟩
    · intro h
      have hloc := (hiff0 a).mpr (fun d hd => h d (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hd)))))
      have h0 : ∀ k : Fin p.length, a k.val = p.getD k.val false := by
        intro k
        obtain ⟨l, hl, hal⟩ := h [(k.val, p.getD k.val false)]
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)))))
        simp only [List.mem_singleton] at hl
        subst hl
        exact hal
      have hout : a (n * b * t) = true := by
        obtain ⟨l, hl, hal⟩ := h [(n * b * t, true)] (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
        simp only [List.mem_singleton] at hl
        subst hl
        exact hal
      exact ⟨⟨h0, hloc⟩, hout⟩
  · simp only [List.length_append, List.length_map, List.length_finRange, List.length_singleton]
    linarith
  · intro d hd l hl
    rcases List.mem_append.mp hd with hd1 | hd2
    · rcases List.mem_append.mp hd1 with hd3 | hd4
      · exact hvar0 d hd3 l hl
      · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd4
        simp only [List.mem_singleton] at hl
        subst hl
        have hk := k.isLt
        have hpl : p.length ≤ n * b * (t + 1) := by nlinarith
        dsimp only
        omega
    · simp only [List.mem_singleton] at hd2
      subst hd2
      simp only [List.mem_singleton] at hl
      subst hl
      dsimp only
      nlinarith

end MPP.Solutions.Pnp321
