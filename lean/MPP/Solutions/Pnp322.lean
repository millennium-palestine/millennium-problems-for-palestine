import Mathlib
import MPP.Solutions.Pnp198
import MPP.Solutions.Pnp200

namespace MPP.Solutions.Pnp322

theorem blockTop (p : List (Bool × Bool))
    (h1 : ∀ j, j ≤ p.length → 0 ≤ ((p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum)
    (h2 : (p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0)
    (v : Bool) (t w : List Bool) :
    ∃ (g : Bool) (w' : List Bool),
      (p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = (g :: t, w', none) ∧
      (p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ([v], w, none) = ([g], w', none) := by
  obtain ⟨g, w', h⟩ := MPP.Solutions.Pnp198.main p h1 h2 t w v
  exact ⟨g, w', h, MPP.Solutions.Pnp200.main p h1 h2 t [] w w' v g h⟩

theorem main : ∀ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
  (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 ∧
    ∀ j, j ≤ b.length → 0 ≤ ((b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
  ∀ (v : Bool) (t w : List Bool),
    ((((items.map fun b => b ++ [(true, true)]).flatten ++ T).flatMap fun r => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)) =
    let ch := items.foldl (fun (s : Bool × List Bool × List Bool) b =>
      let R := (b.flatMap fun r => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ([s.1], s.2.2, none)
      (!(R.1.headD false && s.2.1.headD false), s.2.1.drop 1, R.2.1)) (v, t, w)
    ((T.flatMap fun r => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (ch.1 :: ch.2.1, ch.2.2, none)) := by
  intro items T
  induction items with
  | nil =>
    intro _ v t w
    simp
  | cons b rest ih =>
    intro hb v t w
    have hb0 := hb b (by simp)
    obtain ⟨g, w', h1, h2⟩ := blockTop b hb0.2 hb0.1 v t w
    have hrest := ih (fun b' hb' => hb b' (by simp [hb'])) (!(g && t.headD false)) (t.drop 1) w'
    have hL : ((((b :: rest).map fun b => b ++ [(true, true)]).flatten ++ T).flatMap fun r : Bool × Bool => [r.1, r.2]) =
        (b.flatMap fun r : Bool × Bool => [r.1, r.2]) ++ ([(true, true)].flatMap fun r : Bool × Bool => [r.1, r.2]) ++
        (((rest.map fun b => b ++ [(true, true)]).flatten ++ T).flatMap fun r : Bool × Bool => [r.1, r.2]) := by
      simp [List.append_assoc]
    have hC : ([(true, true)].flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (g :: t, w', none) =
        ((!(g && t.headD false)) :: t.drop 1, w', none) := by
      rfl
    rw [hL, List.foldl_append, List.foldl_append, h1, hC]
    simp only [List.foldl_cons]
    rw [h2]
    exact hrest

end MPP.Solutions.Pnp322
