import Mathlib
import MPP.Solutions.Pnp170
import MPP.Solutions.Pnp173
import MPP.Solutions.Pnp174
import MPP.Solutions.Pnp198

namespace MPP.Solutions.Pnp201

/-- A run over a list of pairs leaves no pending bit when it starts with none. -/
theorem pending_none (L : List (Bool × Bool)) : ∀ (st : List Bool × List Bool × Option Bool),
    st.2.2 = none → ((L.flatMap fun q : Bool × Bool => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st).2.2 = none := by
  induction L with
  | nil => intro st h; simpa using h
  | cons q L ih =>
    intro st h
    obtain ⟨s, w, p⟩ := st
    dsimp only at h
    subst h
    obtain ⟨a, b⟩ := q
    simp only [List.flatMap_cons, List.foldl_append]
    refine ih _ ?_
    cases a <;> cases b <;> rfl

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool), F = (fun (st : List Bool × List Bool × Option Bool) (b : Bool) => match st.2.2 with | none => (st.1, st.2.1, some b) | some a => if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none) else (st.1, st.2.1, none)) else (if b then (st.1.headD false :: st.1, st.2.1, none) else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
  ∀ (ps qs : List (Bool × Bool)),
    (∀ j, j ≤ ps.length → 0 ≤ ((ps.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    (ps.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    (∀ j, j ≤ qs.length → 0 ≤ ((qs.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    (qs.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    ∀ (t : List Bool) (v g : Bool),
      (∃ w : List Bool, w.length = (ps ++ qs).countP (fun q : Bool × Bool => !q.1 && !q.2) ∧ ∃ w' : List Bool,
        ((ps ++ qs).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: t, w, none) = (g :: t, w', none)) ↔
      ∃ g1 : Bool,
        (∃ w : List Bool, w.length = ps.countP (fun q : Bool × Bool => !q.1 && !q.2) ∧ ∃ w' : List Bool,
          (ps.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: t, w, none) = (g1 :: t, w', none)) ∧
        (∃ w : List Bool, w.length = qs.countP (fun q : Bool × Bool => !q.1 && !q.2) ∧ ∃ w' : List Bool,
          (qs.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (g1 :: t, w, none) = (g :: t, w', none)) := by
  intro F hF ps qs hps0 hpsS _ _ t v g
  subst hF
  constructor
  · rintro ⟨w, hw, w', hrun⟩
    have hwlen : w.length = (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)) + (qs.countP (fun q : Bool × Bool => !q.1 && !q.2)) := by
      rw [hw, List.countP_append]
    have htake : (w.take (ps.countP (fun q : Bool × Bool => !q.1 && !q.2))).length = (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)) := by
      rw [List.length_take, hwlen]; omega
    have hdrop : (w.drop (ps.countP (fun q : Bool × Bool => !q.1 && !q.2))).length = (qs.countP (fun q : Bool × Bool => !q.1 && !q.2)) := by
      rw [List.length_drop, hwlen]; omega
    obtain ⟨g1, w1, h1⟩ := MPP.Solutions.Pnp198.main ps hps0 hpsS t (w.take (ps.countP (fun q : Bool × Bool => !q.1 && !q.2))) v
    have h170 := MPP.Solutions.Pnp170.main ps (v :: t) w (w.take (ps.countP (fun q : Bool × Bool => !q.1 && !q.2))) (by rw [List.take_take, min_self])
    have h174 := MPP.Solutions.Pnp174.main ps (v :: t) w
    have hp := pending_none ps (v :: t, w, none) rfl
    have hs1 := congrArg Prod.fst h1
    have hinner : ((ps.flatMap fun q : Bool × Bool => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)) = (g1 :: t, w.drop (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)), none) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact h170.trans hs1
      · exact h174
      · exact hp
    have e := (MPP.Solutions.Pnp173.main ps qs (v :: t) w).symm.trans hrun
    have hq := (congrArg (fun st : List Bool × List Bool × Option Bool => (qs.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st) hinner).symm.trans e
    exact ⟨g1, ⟨w.take (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)), htake, w1, h1⟩, ⟨w.drop (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)), hdrop, w', hq⟩⟩
  · rintro ⟨g1, ⟨w1, hw1, w1', h1⟩, ⟨w2, hw2, w2', h2⟩⟩
    refine ⟨w1 ++ w2, ?_, w2', ?_⟩
    · rw [List.length_append, hw1, hw2, List.countP_append]
    · have htk : (w1 ++ w2).take (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)) = w1.take (ps.countP (fun q : Bool × Bool => !q.1 && !q.2)) := by
        rw [List.take_left' hw1, List.take_of_length_le hw1.le]
      have h170 := MPP.Solutions.Pnp170.main ps (v :: t) (w1 ++ w2) w1 htk
      have h174 := MPP.Solutions.Pnp174.main ps (v :: t) (w1 ++ w2)
      rw [List.drop_left' hw1] at h174
      have hp := pending_none ps (v :: t, w1 ++ w2, none) rfl
      have hs1 := congrArg Prod.fst h1
      have hA : ((ps.flatMap fun q : Bool × Bool => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w1 ++ w2, none)) = (g1 :: t, w2, none) := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact h170.trans hs1
        · exact h174
        · exact hp
      have e2 := (congrArg (fun st : List Bool × List Bool × Option Bool => (qs.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st) hA).trans h2
      exact (MPP.Solutions.Pnp173.main ps qs (v :: t) (w1 ++ w2)).trans e2

end MPP.Solutions.Pnp201
