import Mathlib

namespace MPP.Solutions.Pnp264

-- a balanced nonnegative block, followed by the NAND pair (weight -1), keeps every prefix at least -1
theorem block_prefix (w : Bool × Bool → ℤ) (hw : w (true, true) = -1) (b : List (Bool × Bool))
    (h0 : (b.map w).sum = 0) (hp : ∀ j, j ≤ b.length → 0 ≤ ((b.map w).take j).sum)
    (k : ℕ) (hk : k ≤ b.length + 1) :
    -1 ≤ (((b ++ [(true, true)]).map w).take k).sum := by
  rcases Nat.lt_or_ge k (b.length + 1) with h | h
  · rw [List.map_append, List.take_append_of_le_length (by simp; omega)]
    have := hp k (by omega)
    linarith
  · have hk' : k = b.length + 1 := by omega
    subst hk'
    simp [List.map_append, h0, hw]

theorem main : ∀ items : List (List (Bool × Bool)),
      (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
        ∀ j, j ≤ b.length →
          0 ≤ ((b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      ∀ j, j ≤ ((items.map fun b => b ++ [(true, true)]).flatten).length →
        -(items.length : ℤ) ≤
          ((((items.map fun b => b ++ [(true, true)]).flatten).map fun r : Bool × Bool =>
            if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum := by
  intro items
  induction items with
  | nil =>
    intro _ j hj
    simp at hj
    subst hj
    simp
  | cons b rest ih =>
    intro hitems j hj
    have hb := hitems b (List.mem_cons_self)
    have hrest : ∀ c ∈ rest, (c.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
        ∀ j, j ≤ c.length →
          0 ≤ ((c.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum :=
      fun c hc => hitems c (List.mem_cons_of_mem _ hc)
    have ih' := ih hrest
    generalize hwd : (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) = w at *
    have hw : w (true, true) = -1 := by rw [← hwd]; simp
    have hL := block_prefix w hw b hb.1 hb.2
    have hX : ((b ++ [(true, true)]).map w).sum = -1 := by
      simp [List.map_append, hb.1, hw]
    have hlist : ((b :: rest).map fun b => b ++ [(true, true)]).flatten =
        (b ++ [(true, true)]) ++ (rest.map fun b => b ++ [(true, true)]).flatten := by
      simp
    rw [hlist] at hj ⊢
    rw [List.map_append, List.take_append, List.sum_append]
    have hlenA : ((b ++ [(true, true)]).map w).length = b.length + 1 := by simp
    rcases Nat.lt_or_ge j (b.length + 2) with hlt | hge
    · have hz : j - ((b ++ [(true, true)]).map w).length = 0 := by omega
      rw [hz]
      have h1 := hL j (by omega)
      simp only [List.take_zero, List.sum_nil, add_zero, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · have hjge : ((b ++ [(true, true)]).map w).length ≤ j := by omega
      rw [List.take_of_length_le hjge, hX]
      have h2 := ih' (j - ((b ++ [(true, true)]).map w).length) (by simp at hj ⊢; omega)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

end MPP.Solutions.Pnp264
