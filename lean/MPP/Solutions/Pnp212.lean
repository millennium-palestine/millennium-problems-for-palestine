import Mathlib
import MPP.Solutions.Pnp170
import MPP.Solutions.Pnp174
import MPP.Solutions.Pnp198

namespace MPP.Solutions.Pnp212

/-- One bit of the pnp-133 fold, as a step on (stack, witness, pending bit). -/
def step212 (st : List Bool × List Bool × Option Bool) (b : Bool) : List Bool × List Bool × Option Bool :=
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))

theorem run_copy (v : Bool) (t w : List Bool) :
    [false, true].foldl step212 (v :: t, w, none) = (v :: v :: t, w, none) := rfl

theorem run_leaf (v : Bool) (t w : List Bool) :
    [false, false].foldl step212 (v :: t, w, none) = (w.headD false :: v :: t, w.drop 1, none) := rfl

theorem run_nand (g v : Bool) (t w : List Bool) :
    [true, true].foldl step212 (g :: v :: t, w, none) = ((!(g && v)) :: t, w, none) := rfl

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool), F = (fun (st : List Bool × List Bool × Option Bool) (b : Bool) => match st.2.2 with | none => (st.1, st.2.1, some b) | some a => if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none) else (st.1, st.2.1, none)) else (if b then (st.1.headD false :: st.1, st.2.1, none) else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (a c : Bool × Bool) (mid : List (Bool × Bool)), a.1 = false → c = (true, true) →
    (mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    (∀ j, j ≤ mid.length → 0 ≤ ((mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    ∀ (v g : Bool) (t : List Bool),
      (∃ w : List Bool, w.length = ((a :: (mid ++ [c])).countP fun q : Bool × Bool => !q.1 && !q.2) ∧ ∃ w' : List Bool,
        ((a :: (mid ++ [c])).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: t, w, none) = (g :: t, w', none)) ↔
      ∃ u : Bool, (a.2 = true → u = v) ∧ ∃ g' : Bool,
        (∃ w1 : List Bool, w1.length = (mid.countP fun q : Bool × Bool => !q.1 && !q.2) ∧ ∃ w2 : List Bool,
          (mid.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (u :: v :: t, w1, none) = (g' :: v :: t, w2, none)) ∧
        g = !(g' && v) := by
  intro F hF a c mid ha1 hc hmz hnn v g t
  have hFs : F = step212 := hF
  subst hFs
  subst hc
  obtain ⟨a1, a2⟩ := a
  dsimp only at ha1
  subst ha1
  have hsplit : ((false, a2) :: (mid ++ [((true, true) : Bool × Bool)])).flatMap (fun r : Bool × Bool => [r.1, r.2])
      = [false, a2] ++ ((mid.flatMap fun r : Bool × Bool => [r.1, r.2]) ++ [true, true]) := by
    simp [List.flatMap_append]
  have hcount : ((false, a2) :: (mid ++ [((true, true) : Bool × Bool)])).countP (fun q : Bool × Bool => !q.1 && !q.2)
      = (if a2 then 0 else 1) + mid.countP (fun q : Bool × Bool => !q.1 && !q.2) := by
    cases a2 <;> simp [List.countP_append] <;> omega
  constructor
  · rintro ⟨w, hw, w', hrun⟩
    rw [hcount] at hw
    rw [hsplit, List.foldl_append, List.foldl_append] at hrun
    cases a2
    · rw [run_leaf] at hrun
      obtain ⟨g', w'', h198⟩ := MPP.Solutions.Pnp198.main mid hnn hmz (v :: t) (w.drop 1) (w.headD false)
      have h' : (mid.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl step212 (w.headD false :: v :: t, w.drop 1, none)
          = (g' :: v :: t, w'', none) := h198
      rw [h', run_nand] at hrun
      have hg : g = !(g' && v) := by
        have := congrArg (fun p => p.1.headD false) hrun
        simpa using this.symm
      refine ⟨w.headD false, fun h => by simp at h, g', ⟨w.drop 1, ?_, w'', h'⟩, hg⟩
      simp at hw
      rw [List.length_drop]
      omega
    · rw [run_copy] at hrun
      obtain ⟨g', w'', h198⟩ := MPP.Solutions.Pnp198.main mid hnn hmz (v :: t) w v
      have h' : (mid.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl step212 (v :: v :: t, w, none)
          = (g' :: v :: t, w'', none) := h198
      rw [h', run_nand] at hrun
      have hg : g = !(g' && v) := by
        have := congrArg (fun p => p.1.headD false) hrun
        simpa using this.symm
      refine ⟨v, fun _ => rfl, g', ⟨w, ?_, w'', h'⟩, hg⟩
      simp at hw
      exact hw
  · rintro ⟨u, hu, g', ⟨w1, hw1, w2, hmid⟩, hg⟩
    subst hg
    cases a2
    · have hS : [false, false].foldl step212 (v :: t, u :: w1, none) = (u :: v :: t, w1, none) := rfl
      refine ⟨u :: w1, ?_, w2, ?_⟩
      · rw [hcount]
        simp [hw1]
        omega
      · rw [hsplit, List.foldl_append, List.foldl_append, hS, hmid, run_nand]
    · have hu' : u = v := hu rfl
      subst hu'
      refine ⟨w1, ?_, w2, ?_⟩
      · rw [hcount]
        simp [hw1]
      · rw [hsplit, List.foldl_append, List.foldl_append, run_copy, hmid, run_nand]

end MPP.Solutions.Pnp212
