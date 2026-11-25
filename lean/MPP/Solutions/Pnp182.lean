import Mathlib

namespace MPP.Solutions.Pnp182

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
    (∃ c : ℕ, 5 < c ∧ (1, c) ∈ s.2.2.2) ∧ (∃ c : ℕ, 5 < c ∧ (3, c) ∈ s.2.2.2) ∧
      (∃ c : ℕ, 5 < c ∧ (5, c) ∈ s.2.2.2) ∧
      Relation.ReflTransGen (fun c a => (a, c) ∈ s.2.2.2) 5 1 ∧
      Relation.ReflTransGen (fun c a => (a, c) ∈ s.2.2.2) 5 3 := by
  refine ⟨[false, false, false, true, false, false, true, true, false, true, false, false, true, true,
    true, true, true, true], _, rfl, ⟨7, by decide, by decide⟩, ⟨6, by decide, by decide⟩,
    ⟨6, by decide, by decide⟩, ?_, ?_⟩
  · exact Relation.ReflTransGen.tail (b := 3) (Relation.ReflTransGen.single (by decide)) (by decide)
  · exact Relation.ReflTransGen.single (by decide)

end MPP.Solutions.Pnp182
