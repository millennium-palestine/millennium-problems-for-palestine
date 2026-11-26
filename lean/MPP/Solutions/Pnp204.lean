import Mathlib
import MPP.Solutions.Pnp170
import MPP.Solutions.Pnp173
import MPP.Solutions.Pnp174
import MPP.Solutions.Pnp198

namespace MPP.Solutions.Pnp204

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

theorem main : ∀ (p s : List (Bool × Bool)) (c : Bool × Bool), c = (true, true) →
  (p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
  (∀ j, j ≤ p.length → 0 ≤ ((p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
  ∀ (v : Bool) (t w : List Bool), ∃ g : Bool,
    ((p ++ c :: s).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) =
    ((s.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ((!(g && t.headD false)) :: t.drop 1, w.drop (p.countP fun q : Bool × Bool => !q.1 && !q.2), none)) := by
  intro p s c hc hsum hpos v t w
  subst hc
  have h170 := MPP.Solutions.Pnp170.main p (v :: t) w (w.take (p.countP (fun q : Bool × Bool => !q.1 && !q.2))) (by rw [List.take_take, min_self])
  have h174 := MPP.Solutions.Pnp174.main p (v :: t) w
  have hp := pending_none p (v :: t, w, none) rfl
  obtain ⟨g, w1, h1⟩ := MPP.Solutions.Pnp198.main p hpos hsum t (w.take (p.countP (fun q : Bool × Bool => !q.1 && !q.2))) v
  have hs1 := congrArg Prod.fst h1
  have hinner : ((p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)) = (g :: t, w.drop (p.countP (fun q : Bool × Bool => !q.1 && !q.2)), none) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact h170.trans hs1
    · exact h174
    · exact hp
  have hsplit : ((p ++ (true, true) :: s).flatMap fun r : Bool × Bool => [r.1, r.2]) = (p.flatMap fun r : Bool × Bool => [r.1, r.2]) ++ ([true, true] ++ (s.flatMap fun r : Bool × Bool => [r.1, r.2])) := by
    simp
  refine ⟨g, ?_⟩
  rw [hsplit, List.foldl_append, List.foldl_append]
  exact congrArg (fun st => List.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (List.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st [true, true]) (s.flatMap fun r : Bool × Bool => [r.1, r.2])) hinner

end MPP.Solutions.Pnp204
