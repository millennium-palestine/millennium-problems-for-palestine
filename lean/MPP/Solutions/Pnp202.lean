import Mathlib
import MPP.Solutions.Pnp198

namespace MPP.Solutions.Pnp202

theorem main : ∀ (a c : Bool × Bool) (mid : List (Bool × Bool)), a.1 = false → c = (true, true) →
  (mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
  (∀ j, j ≤ mid.length → 0 ≤ ((mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
  ∀ (v : Bool) (t w : List Bool), ∃ (g : Bool) (w' : List Bool),
    ((a :: (mid ++ [c])).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = ((!(g && v)) :: t, w', none) := by
  intro a c mid ha hc hsum hpos v t w
  obtain ⟨a1, a2⟩ := a
  have ha' : a1 = false := ha
  subst ha'
  subst hc
  have hup : ∃ (u : Bool) (w0 : List Bool),
      (List.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) ((([((false, a2) : Bool × Bool)]).flatMap fun r : Bool × Bool => [r.1, r.2]))) = (u :: v :: t, w0, none) := by
    cases a2
    · exact ⟨w.headD false, w.drop 1, rfl⟩
    · exact ⟨v, w, rfl⟩
  obtain ⟨u, w0, hu⟩ := hup
  have hsplit : ((((false, a2) : Bool × Bool) :: (mid ++ [((true, true) : Bool × Bool)])).flatMap fun r : Bool × Bool => [r.1, r.2])
      = (([((false, a2) : Bool × Bool)]).flatMap fun r : Bool × Bool => [r.1, r.2]) ++ (mid.flatMap fun r : Bool × Bool => [r.1, r.2]) ++ [true, true] := by
    simp
  obtain ⟨g, w2, hm⟩ := MPP.Solutions.Pnp198.main mid hpos hsum (v :: t) w0 u
  refine ⟨g, w2, ?_⟩
  rw [hsplit, List.foldl_append, List.foldl_append]
  exact congrArg (fun st => List.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st [true, true]) ((congrArg (fun st => List.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st (mid.flatMap fun r : Bool × Bool => [r.1, r.2])) hu).trans hm)

end MPP.Solutions.Pnp202
