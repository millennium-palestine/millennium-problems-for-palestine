import Mathlib
import MPP.Solutions.Pnp303

namespace MPP.Solutions.Pnp316

-- the length of a flattened list of lists is at most the outer length times the bound
theorem flat_len {α β : Type} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  rw [List.length_flatMap]
  have hsum := List.sum_le_card_nsmul (l.map fun x => (f x).length) M (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx)
  simp only [List.length_map, smul_eq_mul] at hsum ⊢
  exact hsum

theorem main : ∀ (n b t : ℕ) (G : Fin b → (Fin (3 * b) → Bool) → Bool), ∃ D : List (List (ℕ × Bool)),
    (∀ a : ℕ → Bool, (∀ s : Fin t, ∀ i : Fin n, ∀ j : Fin b,
      a (n * b * (s.val + 1) + i.val * b + j.val) =
        G j (fun k : Fin (3 * b) => a (n * b * s.val + ((i.val + k.val / b) % n) * b + k.val % b))) ↔
      ∀ d ∈ D, ∃ l ∈ d, a l.1 = l.2) ∧
    D.length ≤ 2 ^ (3 * b + 1) * (n * b * t) ∧ ∀ d ∈ D, ∀ l ∈ d, l.1 < n * b * (t + 1) := by
  intro n b t G
  -- one truth-table CNF for each cell i, bit j, of row s + 1
  have hblock : ∀ (s : Fin t) (i : Fin n) (j : Fin b), ∃ C : List (List (ℕ × Bool)),
      (∀ a : ℕ → Bool, (∀ c ∈ C, ∃ l ∈ c, a l.1 = l.2) ↔
        a (n * b * (s.val + 1) + i.val * b + j.val) =
          G j (fun k : Fin (3 * b) => a (n * b * s.val + ((i.val + k.val / b) % n) * b + k.val % b))) ∧
      C.length ≤ 2 ^ (3 * b + 1) ∧ ∀ c ∈ C, ∀ l ∈ c, l.1 < n * b * (s.val + 2) := by
    intro s i j
    obtain ⟨C, hC, hlen, hvar⟩ := MPP.Solutions.Pnp303.tt_cnf (3 * b + 1)
      (fun c : Fin (3 * b + 1) → Bool =>
        (c (Fin.last (3 * b)) == G j (fun k : Fin (3 * b) => c (Fin.castSucc k))))
      (fun v : Fin (3 * b + 1) => if v.val < 3 * b then
        n * b * s.val + ((i.val + v.val / b) % n) * b + v.val % b
        else n * b * (s.val + 1) + i.val * b + j.val)
    refine ⟨C, fun a => ?_, hlen, fun c hc l hl => ?_⟩
    · refine (hC a).trans ?_
      simp only [beq_iff_eq, Fin.val_last, Fin.val_castSucc, Fin.is_lt, lt_self_iff_false,
        if_true, if_false]
    · obtain ⟨v, hv⟩ := hvar c hc l hl
      rw [hv]
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
      have e : n * b * (s.val + 2) = n * b * s.val + n * b + n * b := by ring
      have e' : n * b * (s.val + 1) = n * b * s.val + n * b := by ring
      split_ifs with h3
      · have hb : 0 < b := by omega
        have hq := Nat.mod_lt v.val hb
        have hr := Nat.mod_lt (i.val + v.val / b) hn
        generalize (i.val + v.val / b) % n = r at hr ⊢
        generalize v.val % b = q at hq ⊢
        have key1 : (r + 1) * b ≤ n * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hr)
        have key2 : (r + 1) * b = r * b + b := by ring
        omega
      · have key1 : (i.val + 1) * b ≤ n * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt)
        have key2 : (i.val + 1) * b = i.val * b + b := by ring
        have hj := j.isLt
        omega
  choose C hC hlen hvar using hblock
  refine ⟨(List.finRange t).flatMap (fun s => (List.finRange n).flatMap
    (fun i => (List.finRange b).flatMap (fun j => C s i j))), ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h d hd
      obtain ⟨s, _, hd1⟩ := List.mem_flatMap.mp hd
      obtain ⟨i, _, hd2⟩ := List.mem_flatMap.mp hd1
      obtain ⟨j, _, hd3⟩ := List.mem_flatMap.mp hd2
      exact (hC s i j a).mpr (h s i j) d hd3
    · intro h s i j
      apply (hC s i j a).mp
      intro c hc
      exact h c (List.mem_flatMap.mpr ⟨s, List.mem_finRange s,
        List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
          List.mem_flatMap.mpr ⟨j, List.mem_finRange j, hc⟩⟩⟩)
  · have hi : ∀ s : Fin t, ∀ i : Fin n,
        ((List.finRange b).flatMap (fun j => C s i j)).length ≤ b * 2 ^ (3 * b + 1) := by
      intro s i
      have := flat_len (List.finRange b) (fun j => C s i j) (2 ^ (3 * b + 1))
        (fun j _ => hlen s i j)
      simpa using this
    have hm : ∀ s : Fin t, ((List.finRange n).flatMap (fun i =>
        (List.finRange b).flatMap (fun j => C s i j))).length ≤ n * (b * 2 ^ (3 * b + 1)) := by
      intro s
      have := flat_len (List.finRange n) (fun i => (List.finRange b).flatMap (fun j => C s i j))
        (b * 2 ^ (3 * b + 1)) (fun i _ => hi s i)
      simpa using this
    have hout := flat_len (List.finRange t) (fun s => (List.finRange n).flatMap
        (fun i => (List.finRange b).flatMap (fun j => C s i j))) (n * (b * 2 ^ (3 * b + 1)))
      (fun s _ => hm s)
    simp only [List.length_finRange] at hout
    calc _ ≤ t * (n * (b * 2 ^ (3 * b + 1))) := hout
      _ = 2 ^ (3 * b + 1) * (n * b * t) := by ring
  · intro d hd l hl
    obtain ⟨s, _, hd1⟩ := List.mem_flatMap.mp hd
    obtain ⟨i, _, hd2⟩ := List.mem_flatMap.mp hd1
    obtain ⟨j, _, hd3⟩ := List.mem_flatMap.mp hd2
    have h1 := hvar s i j d hd3 l hl
    have h2 : n * b * (s.val + 2) ≤ n * b * (t + 1) :=
      Nat.mul_le_mul_left (n * b) (by have := s.isLt; omega)
    omega

end MPP.Solutions.Pnp316
