import Mathlib
import MPP.Solutions.Pnp162

namespace MPP.Solutions.Pnp163

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
    ∀ p ∈ s.2.2.2, ∀ q ∈ s.2.2.2, p.1 < q.1 → q.1 < p.2 → q.2 ≤ p.2 := by
  intro x s hs p hp q hq hpq hqp
  by_contra hc
  push_neg at hc
  exact MPP.Solutions.Pnp162.main x s hs p hp q hq ⟨hpq, hqp, hc⟩

end MPP.Solutions.Pnp163
