import Mathlib
import MPP.Solutions.Pnp201
import MPP.Solutions.Pnp211
import MPP.Solutions.Pnp212

namespace MPP.Solutions.Pnp213

open MPP.Solutions.Pnp212

theorem run_noop (v : Bool) (t w : List Bool) :
    [true, false].foldl step212 (v :: t, w, none) = (v :: t, w, none) := rfl

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool), F = (fun st b => match st.2.2 with | none => (st.1, st.2.1, some b) | some a => if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none) else (st.1, st.2.1, none)) else (if b then (st.1.headD false :: st.1, st.2.1, none) else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (H : Bool × Bool → ℤ), H = (fun r => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) →
    ∀ q : List (Bool × Bool), 0 < q.length → (∀ j, j ≤ q.length → 0 ≤ ((q.map H).take j).sum) → (q.map H).sum = 0 →
    ∀ (v g : Bool) (t : List Bool),
      (∃ w : List Bool, w.length = q.countP (fun x => !x.1 && !x.2) ∧ ∃ w' : List Bool,
        (q.flatMap fun r => [r.1, r.2]).foldl F (v :: t, w, none) = (g :: t, w', none)) ↔
      (q = [(true, false)] ∧ g = v) ∨
      (∃ (a c : Bool × Bool) (mid : List (Bool × Bool)), q = a :: (mid ++ [c]) ∧ a.1 = false ∧ c = (true, true) ∧
        (mid.map H).sum = 0 ∧ (∀ j, j ≤ mid.length → 0 ≤ ((mid.map H).take j).sum) ∧
        ∃ u : Bool, (a.2 = true → u = v) ∧ ∃ g' : Bool,
          (∃ w1 : List Bool, w1.length = mid.countP (fun x => !x.1 && !x.2) ∧ ∃ w2 : List Bool,
            (mid.flatMap fun r => [r.1, r.2]).foldl F (u :: v :: t, w1, none) = (g' :: v :: t, w2, none)) ∧
          g = !(g' && v)) ∨
      (∃ p s : List (Bool × Bool), q = p ++ s ∧ 0 < p.length ∧ 0 < s.length ∧
        (∀ j, j ≤ p.length → 0 ≤ ((p.map H).take j).sum) ∧ (p.map H).sum = 0 ∧
        (∀ j, j ≤ s.length → 0 ≤ ((s.map H).take j).sum) ∧ (s.map H).sum = 0 ∧
        ∃ g1 : Bool,
          (∃ w : List Bool, w.length = p.countP (fun x => !x.1 && !x.2) ∧ ∃ w' : List Bool,
            (p.flatMap fun r => [r.1, r.2]).foldl F (v :: t, w, none) = (g1 :: t, w', none)) ∧
          (∃ w : List Bool, w.length = s.countP (fun x => !x.1 && !x.2) ∧ ∃ w' : List Bool,
            (s.flatMap fun r => [r.1, r.2]).foldl F (g1 :: t, w, none) = (g :: t, w', none))) := by
  intro F hF H hH q hq hnn hz v g t
  have hFs : F = step212 := hF
  subst hFs
  subst hH
  constructor
  · rintro ⟨w, hw, w', hrun⟩
    rcases MPP.Solutions.Pnp211.main q hq hnn hz with rfl | ⟨a, c, mid, rfl, ha1, hc, hmid, hmidnn⟩ |
      ⟨p, s, rfl, hp0, hs0, hpnn, hpz, hsnn, hsz⟩
    · left
      refine ⟨rfl, ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hrun
      rw [run_noop] at hrun
      have := congrArg (fun p => p.1.headD false) hrun
      simpa using this.symm
    · right; left
      have hL := (MPP.Solutions.Pnp212.main _ hF a c mid ha1 hc hmid hmidnn v g t).1 ⟨w, hw, w', hrun⟩
      exact ⟨a, c, mid, rfl, ha1, hc, hmid, hmidnn, hL⟩
    · right; right
      have hL := (MPP.Solutions.Pnp201.main _ hF p s hpnn hpz hsnn hsz t v g).1 ⟨w, hw, w', hrun⟩
      exact ⟨p, s, rfl, hp0, hs0, hpnn, hpz, hsnn, hsz, hL⟩
  · rintro (⟨rfl, rfl⟩ | ⟨a, c, mid, rfl, ha1, hc, hmid, hmidnn, hR⟩ |
      ⟨p, s, rfl, hp0, hs0, hpnn, hpz, hsnn, hsz, hR⟩)
    · refine ⟨[], rfl, [], ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact run_noop _ _ _
    · exact (MPP.Solutions.Pnp212.main _ hF a c mid ha1 hc hmid hmidnn v g t).2 hR
    · exact (MPP.Solutions.Pnp201.main _ hF p s hpnn hpz hsnn hsz t v g).2 hR

end MPP.Solutions.Pnp213
