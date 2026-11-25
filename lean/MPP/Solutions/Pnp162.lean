import Mathlib

namespace MPP.Solutions.Pnp162

theorem main : ∀ (x : List Bool) (s : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
    x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
      match st.2.2.1 with
      | none => (st.1, st.2.1, some b, st.2.2.2)
      | some a =>
        if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
            ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
          else (st.1, st.2.1, none, st.2.2.2))
        else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
          else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) ([], 1, none, []) = s →
    ∀ p ∈ s.2.2.2, ∀ q ∈ s.2.2.2, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) := by
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      (st.1.Pairwise (· ≥ ·) ∧ (∀ w ∈ st.1, w < st.2.1) ∧ 1 ≤ st.2.1 ∧
        (∀ p ∈ st.2.2.2, p.1 < p.2 ∧ p.2 < st.2.1) ∧
        (∀ p ∈ st.2.2.2, ∀ w ∈ st.1, ¬ (p.1 < w ∧ w < p.2)) ∧
        (∀ p ∈ st.2.2.2, ∀ q ∈ st.2.2.2, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))) →
      ∀ s : List ℕ × ℕ × Option Bool × List (ℕ × ℕ),
        x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st = s →
        (s.1.Pairwise (· ≥ ·) ∧ (∀ w ∈ s.1, w < s.2.1) ∧ 1 ≤ s.2.1 ∧
          (∀ p ∈ s.2.2.2, p.1 < p.2 ∧ p.2 < s.2.1) ∧
          (∀ p ∈ s.2.2.2, ∀ w ∈ s.1, ¬ (p.1 < w ∧ w < p.2)) ∧
          (∀ p ∈ s.2.2.2, ∀ q ∈ s.2.2.2, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))) := by
    intro x
    induction x with
    | nil =>
      intro st hst s hs
      subst hs
      exact hst
    | cons b xs ih =>
      intro st hst s hs
      rw [List.foldl_cons] at hs
      refine ih _ ?_ s hs
      rcases st with ⟨stk, t, pend, arcs⟩
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
      dsimp only at h1 h2 h3 h4 h5 h6 ⊢
      cases pend with
      | none => exact ⟨h1, h2, h3, h4, h5, h6⟩
      | some a =>
        cases a <;> cases b <;> try dsimp only
        · -- leaf: push the time and advance it; no arc is made
          refine ⟨List.pairwise_cons.2 ⟨fun y hy => (h2 y hy).le, h1⟩, ?_,
            Nat.le_succ_of_le h3, ?_, ?_, h6⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h2 w hw)
          · intro p hp
            exact ⟨(h4 p hp).1, Nat.lt_succ_of_lt (h4 p hp).2⟩
          · intro p hp w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · intro hc
              have := (h4 p hp).2
              obtain ⟨_, hc2⟩ := hc
              omega
            · exact h5 p hp w hw
        · -- copy: push the top entry (0 on an empty stack); no arc is made
          cases stk with
          | nil =>
            refine ⟨by simp, ?_, h3, h4, ?_, h6⟩
            · intro w hw
              simp at hw
              subst hw
              exact h3
            · intro p hp w hw
              simp at hw
              subst hw
              intro hc
              exact absurd hc.1 (Nat.not_lt_zero _)
          | cons x rest =>
            have hx : x < t := h2 x (by simp)
            refine ⟨?_, ?_, h3, h4, ?_, h6⟩
            · refine List.pairwise_cons.2 ⟨?_, h1⟩
              intro y hy
              rcases List.mem_cons.1 hy with rfl | hy'
              · exact le_refl _
              · exact (List.pairwise_cons.1 h1).1 y hy'
            · intro w hw
              rcases List.mem_cons.1 hw with h | hw
              · rw [h]
                simpa using hx
              · exact h2 w hw
            · intro p hp w hw
              rcases List.mem_cons.1 hw with h | hw
              · exact h5 p hp w (by rw [h]; simp)
              · exact h5 p hp w hw
        · -- (true, false): nothing happens
          exact ⟨h1, h2, h3, h4, h5, h6⟩
        · -- NAND: pop two, push the time t, and record the arcs (u, t)
          have hpa : (stk.take 2 ++ stk.drop 2).Pairwise (· ≥ ·) := by
            rw [List.take_append_drop]
            exact h1
          have hsplit := (List.pairwise_append.1 hpa).2.2
          have hsub1 : ∀ y ∈ stk.drop 2, y ∈ stk := fun y hy => (List.drop_sublist 2 stk).subset hy
          have htake : ∀ y ∈ stk.take 2, y ∈ stk := fun y hy => List.take_subset 2 stk hy
          refine ⟨List.pairwise_cons.2 ⟨fun y hy => (h2 y (hsub1 y hy)).le,
            List.Pairwise.sublist (List.drop_sublist 2 stk) h1⟩, ?_, Nat.le_succ_of_le h3, ?_, ?_, ?_⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h2 w (hsub1 w hw))
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · obtain ⟨u, hu, hup⟩ := List.mem_map.1 hp
              subst hup
              have hu1 := (List.mem_filter.1 hu).1
              exact ⟨h2 u (htake u hu1), Nat.lt_succ_self _⟩
            · exact ⟨(h4 p hp).1, Nat.lt_succ_of_lt (h4 p hp).2⟩
          · intro p hp w hw
            rcases List.mem_cons.1 hw with hwt | hw
            · rw [hwt]
              rcases List.mem_append.1 hp with hp | hp
              · obtain ⟨u, hu, hup⟩ := List.mem_map.1 hp
                subst hup
                intro hc
                exact lt_irrefl _ hc.2
              · intro hc
                have := (h4 p hp).2
                exact lt_asymm hc.2 this
            · rcases List.mem_append.1 hp with hp | hp
              · obtain ⟨u, hu, hup⟩ := List.mem_map.1 hp
                subst hup
                have hu1 := (List.mem_filter.1 hu).1
                intro hc
                exact absurd hc.1 (not_lt.2 (hsplit u hu1 w hw))
              · exact h5 p hp w (hsub1 w hw)
          · intro p hp q hq
            rcases List.mem_append.1 hp with hp | hp
            · obtain ⟨u, hu, hup⟩ := List.mem_map.1 hp
              subst hup
              rcases List.mem_append.1 hq with hq | hq
              · obtain ⟨v, hv, hvq⟩ := List.mem_map.1 hq
                subst hvq
                intro hc
                exact lt_irrefl _ hc.2.2
              · intro hc
                have := (h4 q hq).2
                exact absurd hc.2.2 (not_lt.2 this.le)
            · rcases List.mem_append.1 hq with hq | hq
              · obtain ⟨v, hv, hvq⟩ := List.mem_map.1 hq
                subst hvq
                intro hc
                exact h5 p hp v (htake v (List.mem_filter.1 hv).1) ⟨hc.1, hc.2.1⟩
              · exact h6 p hp q hq
  intro x s h
  have hs := key x ([], 1, none, [])
    ⟨List.Pairwise.nil, fun w hw => by simp at hw, le_refl 1,
      fun p hp => by simp at hp, fun p hp => by simp at hp,
      fun p hp q hq => by simp at hp⟩ s h
  exact hs.2.2.2.2.2

end MPP.Solutions.Pnp162
