import Mathlib

namespace MPP.Solutions.Pnp303

theorem tt_cnf : ∀ (k : ℕ) (G : (Fin k → Bool) → Bool) (φ : Fin k → ℕ),
    ∃ C : List (List (ℕ × Bool)),
    (∀ a : ℕ → Bool, (∀ c ∈ C, ∃ l ∈ c, a l.1 = l.2) ↔ G (fun v => a (φ v)) = true) ∧
    C.length ≤ 2 ^ k ∧ ∀ c ∈ C, ∀ l ∈ c, ∃ v, l.1 = φ v := by
  intro k G φ
  refine ⟨(Finset.univ.filter (fun b : Fin k → Bool => G b = false)).toList.map
      (fun b => List.ofFn (fun v : Fin k => (φ v, !b v))), ?_, ?_, ?_⟩
  · intro a
    have key : ∀ b : Fin k → Bool,
        (∃ l ∈ List.ofFn (fun v : Fin k => (φ v, !b v)), a l.1 = l.2) ↔
          (fun v => a (φ v)) ≠ b := by
      intro b
      constructor
      · rintro ⟨l, hl, hal⟩ hab
        obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hl
        have h1 : a (φ v) = b v := congrFun hab v
        change a (φ v) = !b v at hal
        rw [h1] at hal
        cases h : b v <;> simp [h] at hal
      · intro hne
        by_contra hno
        apply hne
        funext v
        by_contra hv
        apply hno
        refine ⟨(φ v, !b v), List.mem_ofFn.mpr ⟨v, rfl⟩, ?_⟩
        change a (φ v) = !b v
        cases ha : a (φ v) <;> cases hb : b v <;> simp_all
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      key, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      by_contra hga
      have hfalse : G (fun v => a (φ v)) = false := by simpa using hga
      exact ha _ hfalse rfl
    · intro h b hb hab
      subst hab
      rw [h] at hb
      exact Bool.noConfusion hb
  · rw [List.length_map, Finset.length_toList]
    exact (Finset.card_filter_le _ _).trans (by simp)
  · intro c hc l hl
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    simp only [List.mem_ofFn] at hl
    obtain ⟨v, rfl⟩ := hl
    exact ⟨v, rfl⟩

-- one row of the window rule, read at the offset o
theorem row_off : ∀ (n o : ℕ) (g : (Fin 3 → Bool) → Bool), ∃ D : List (List (ℕ × Bool)),
    (∀ a : ℕ → Bool, (∀ i : Fin n, a (o + n + i.val) = g (fun j => a (o + (i.val + j.val) % n))) ↔
      ∀ d ∈ D, ∃ l ∈ d, a l.1 = l.2) ∧
    D.length ≤ 16 * n ∧ ∀ d ∈ D, ∀ l ∈ d, l.1 < o + 2 * n := by
  intro n o g
  have hloc : ∀ i : Fin n, ∃ C : List (List (ℕ × Bool)),
      (∀ a : ℕ → Bool, (∀ c ∈ C, ∃ l ∈ c, a l.1 = l.2) ↔
        a (o + n + i.val) = g (fun j => a (o + (i.val + j.val) % n))) ∧
      C.length ≤ 16 ∧ ∀ c ∈ C, ∀ l ∈ c, l.1 < o + 2 * n := by
    intro i
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    obtain ⟨C, hC, hlen, hvar⟩ := tt_cnf 4
      (fun b : Fin 4 → Bool => (b 3 == g (fun j => b (Fin.castSucc j))))
      (fun v : Fin 4 => if v.val < 3 then o + (i.val + v.val) % n else o + n + i.val)
    refine ⟨C, fun a => ?_, le_trans hlen (by norm_num), fun c hc l hl => ?_⟩
    · rw [hC a]
      have h3 : (if (3 : Fin 4).val < 3 then o + (i.val + (3 : Fin 4).val) % n else o + n + i.val)
          = o + n + i.val := by simp
      have hw : (fun j : Fin 3 => a (if (Fin.castSucc j).val < 3 then
            o + (i.val + (Fin.castSucc j).val) % n else o + n + i.val))
          = fun j : Fin 3 => a (o + (i.val + j.val) % n) := by
        funext j
        simp [j.isLt]
      simp only [beq_iff_eq]
      rw [h3, hw]
    · obtain ⟨v, hv⟩ := hvar c hc l hl
      rw [hv]
      have hi := i.isLt
      split_ifs with hv3
      · have hmod := Nat.mod_lt (i.val + v.val) hn
        generalize (i.val + v.val) % n = r at hmod ⊢
        omega
      · omega
  choose C hC hlen hvar using hloc
  refine ⟨(List.finRange n).flatMap (fun i => C i), ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h d hd
      obtain ⟨i, _, hdi⟩ := List.mem_flatMap.mp hd
      exact (hC i a).mpr (h i) d hdi
    · intro h i
      apply (hC i a).mp
      intro c hc
      exact h c (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hc⟩)
  · have hsum := List.sum_le_card_nsmul ((List.finRange n).map fun i => (C i).length) 16
      (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact hlen i)
    rw [List.length_flatMap]
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at hsum ⊢
    rw [mul_comm]
    exact hsum
  · intro d hd l hl
    obtain ⟨i, _, hdi⟩ := List.mem_flatMap.mp hd
    exact hvar i d hdi l hl

theorem main : ∀ (n t : ℕ) (g : (Fin 3 → Bool) → Bool), ∃ D : List (List (ℕ × Bool)),
    (∀ a : ℕ → Bool, (∀ s : Fin t, ∀ i : Fin n,
      a (n * (s.val + 1) + i.val) = g (fun j => a (n * s.val + (i.val + j.val) % n))) ↔
      ∀ d ∈ D, ∃ l ∈ d, a l.1 = l.2) ∧
    D.length ≤ 16 * n * t ∧ ∀ d ∈ D, ∀ l ∈ d, l.1 < n * (t + 1) := by
  intro n t g
  have hrow : ∀ s : Fin t, ∃ C : List (List (ℕ × Bool)),
      (∀ a : ℕ → Bool, (∀ i : Fin n,
        a (n * s.val + n + i.val) = g (fun j => a (n * s.val + (i.val + j.val) % n))) ↔
        ∀ c ∈ C, ∃ l ∈ c, a l.1 = l.2) ∧
      C.length ≤ 16 * n ∧ ∀ c ∈ C, ∀ l ∈ c, l.1 < n * s.val + 2 * n := by
    intro s
    obtain ⟨C, hC, hlen, hvar⟩ := row_off n (n * s.val) g
    exact ⟨C, hC, hlen, hvar⟩
  choose C hC hlen hvar using hrow
  refine ⟨(List.finRange t).flatMap (fun s => C s), ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h d hd
      obtain ⟨s, _, hds⟩ := List.mem_flatMap.mp hd
      refine (hC s a).mp ?_ d hds
      intro i
      have hi := h s i
      rwa [show n * (s.val + 1) = n * s.val + n by ring] at hi
    · intro h s i
      rw [show n * (s.val + 1) = n * s.val + n by ring]
      exact (hC s a).mpr (fun d hd => h d (List.mem_flatMap.mpr ⟨s, List.mem_finRange s, hd⟩)) i
  · have hsum := List.sum_le_card_nsmul ((List.finRange t).map fun s => (C s).length) (16 * n)
      (by
        intro x hx
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
        exact hlen s)
    rw [List.length_flatMap]
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at hsum ⊢
    calc _ ≤ t * (16 * n) := hsum
      _ = 16 * n * t := by ring
  · intro d hd l hl
    obtain ⟨s, _, hds⟩ := List.mem_flatMap.mp hd
    have h1 := hvar s d hds l hl
    have h2 : n * (s.val + 2) ≤ n * (t + 1) := Nat.mul_le_mul_left n (by have := s.isLt; omega)
    have h3 : n * (s.val + 2) = n * s.val + 2 * n := by ring
    omega

end MPP.Solutions.Pnp303
