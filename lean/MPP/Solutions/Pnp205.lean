import Mathlib

namespace MPP.Solutions.Pnp205

theorem main : ∀ (mid : List (Bool × Bool)) (v : Bool) (t w w1 : List Bool) (g : Bool),
    ((mid.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: v :: t, w, none) = (g :: v :: t, w1, none)) →
    ((((false, true) :: (mid ++ [(true, true)])).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = ((!(g && v)) :: t, w1, none)) := by
  intro mid v t w w1 g h
  have hflat : (((false, true) :: (mid ++ [(true, true)])).flatMap fun r : Bool × Bool => [r.1, r.2]) =
      [false, true] ++ ((mid.flatMap fun r : Bool × Bool => [r.1, r.2]) ++ [true, true]) := by
    simp
  rw [hflat, List.foldl_append, List.foldl_append]
  have h1 : [false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = (v :: v :: t, w, none) := rfl
  rw [h1, h]
  rfl

end MPP.Solutions.Pnp205
