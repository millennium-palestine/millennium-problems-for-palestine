import Mathlib

namespace MPP.Solutions.Pnp181

theorem main : ∃ x : List Bool, ∃ s : List ℕ × ℕ × Option Bool × List (ℕ × ℕ),
    x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
      match st.2.2.1 with
      | none => (st.1, st.2.1, some b, st.2.2.2)
      | some a =>
        if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
            ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
          else (st.1, st.2.1, none, st.2.2.2))
        else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
          else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) ([], 1, none, []) = s ∧
    ∃ e ∈ s.1, ∃ g ∈ s.1, ∃ f ∈ s.1, f < g ∧ g < e ∧
      Relation.ReflTransGen (fun c a => (a, c) ∈ s.2.2.2) e f := by
  refine ⟨[false, false, false, true, false, false, true, true, false, true, false, false, true, true], _, rfl, ?_⟩
  refine ⟨5, by decide, 3, by decide, 1, by decide, by decide, by decide, ?_⟩
  exact Relation.ReflTransGen.tail (b := 3) (Relation.ReflTransGen.single (by decide)) (by decide)

end MPP.Solutions.Pnp181
