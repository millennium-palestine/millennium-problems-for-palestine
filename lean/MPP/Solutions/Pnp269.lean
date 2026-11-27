import Mathlib
import MPP.Solutions.Pnp263
import MPP.Solutions.Pnp268

namespace MPP.Solutions.Pnp269

theorem main : ∀ (q : List (Bool × Bool)) (v : Bool) (t w : List Bool), ∃ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
    q = (items.map fun b => b ++ [(true, true)]).flatten ++ T ∧
    (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
      ∀ j, j ≤ b.length → 0 ≤ ((b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∧
    (∀ j, j ≤ T.length → 0 ≤ ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) ∧
    ∃ g : Bool, ((q.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)) =
      ((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (g :: t.drop items.length, w.drop (items.flatten.countP fun q : Bool × Bool => !q.1 && !q.2), none)) := by
  intro q v t w
  obtain ⟨items, T, hq, hitems, hT⟩ := MPP.Solutions.Pnp263.main q
  refine ⟨items, T, hq, hitems, hT, ?_⟩
  subst hq
  exact MPP.Solutions.Pnp268.main items T hitems v t w

end MPP.Solutions.Pnp269
