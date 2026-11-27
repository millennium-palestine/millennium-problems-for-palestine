import Mathlib
import MPP.Solutions.Pnp204

namespace MPP.Solutions.Pnp268

theorem main : ∀ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
    (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
      ∀ j, j ≤ b.length → 0 ≤ ((b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    ∀ (v : Bool) (t w : List Bool), ∃ g : Bool,
      ((((items.map fun b => b ++ [(true, true)]).flatten ++ T).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
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
  intro items
  induction items with
  | nil =>
    intro T _ v t w
    exact ⟨v, by simp⟩
  | cons b rest ih =>
    intro T hyp v t w
    have hb := hyp b (by simp)
    have hrest : ∀ b' ∈ rest, (b'.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
        ∀ j, j ≤ b'.length → 0 ≤ ((b'.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum :=
      fun b' hb' => hyp b' (by simp [hb'])
    obtain ⟨g, hg⟩ := MPP.Solutions.Pnp204.main b ((rest.map fun b => b ++ [(true, true)]).flatten ++ T) (true, true) rfl hb.1 hb.2 v t w
    obtain ⟨g', hg'⟩ := ih T hrest (!(g && t.headD false)) (t.drop 1) (w.drop (b.countP fun q : Bool × Bool => !q.1 && !q.2))
    have e1 : ((b :: rest).map fun b => b ++ [(true, true)]).flatten ++ T = b ++ (true, true) :: ((rest.map fun b => b ++ [(true, true)]).flatten ++ T) := by
      simp [List.append_assoc]
    refine ⟨g', ?_⟩
    rw [e1]
    refine Eq.trans hg ?_
    refine Eq.trans hg' ?_
    simp only [List.length_cons, List.flatten_cons, List.countP_append, List.drop_drop]
    rw [Nat.add_comm 1 rest.length]

end MPP.Solutions.Pnp268
