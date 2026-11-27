import Mathlib

namespace MPP.Solutions.Pnp270

theorem headD_eq_getD_zero (l : List Bool) : l.headD false = l.getD 0 false := by
  cases l <;> rfl

theorem agree_step
    (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hF : F = fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none)))
    (k1 k2 w1 w2 : List Bool) (p1 p2 : Option Bool) (b : Bool)
    (hw : w1 = w2) (hp : p1 = p2) (hs : ∀ i, k1.getD i false = k2.getD i false) :
    (F (k1, w1, p1) b).2.1 = (F (k2, w2, p2) b).2.1 ∧
      (F (k1, w1, p1) b).2.2 = (F (k2, w2, p2) b).2.2 ∧
      ∀ i, (F (k1, w1, p1) b).1.getD i false = (F (k2, w2, p2) b).1.getD i false := by
  subst hF hw hp
  have h0 : k1.headD false = k2.headD false := by
    rw [headD_eq_getD_zero, headD_eq_getD_zero]; exact hs 0
  have h1 : (k1.drop 1).headD false = (k2.drop 1).headD false := by
    rw [headD_eq_getD_zero, headD_eq_getD_zero]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using hs 1
  have hd2 : ∀ i, (k1.drop 2).getD i false = (k2.drop 2).getD i false := by
    intro i
    have h := hs (i + 2)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at h ⊢
    rw [Nat.add_comm 2 i]
    exact h
  cases p1 with
  | none =>
    dsimp only
    exact ⟨rfl, rfl, hs⟩
  | some a =>
    cases a <;> cases b <;> dsimp only
    · -- a = false, b = false: leaf pushes the witness head
      refine ⟨rfl, rfl, fun i => ?_⟩
      cases i with
      | zero => simp
      | succ i => simpa using hs i
    · -- a = false, b = true: copy the top
      refine ⟨rfl, rfl, fun i => ?_⟩
      cases i with
      | zero => exact h0
      | succ i => simpa using hs i
    · -- a = true, b = false: nothing happens
      exact ⟨rfl, rfl, hs⟩
    · -- a = true, b = true: NAND of the top two, pop two, push one
      refine ⟨rfl, rfl, fun i => ?_⟩
      rw [h0, h1]
      cases i with
      | zero => rfl
      | succ i => simpa using hd2 i

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool),
    F = (fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (bits w : List Bool),
      (bits.foldl F ([], w, none)).1.headD false = (bits.foldl F ([false], w, none)).1.headD false := by
  intro F hF bits w
  have key : ∀ (bs : List Bool) (k1 k2 w1 w2 : List Bool) (p1 p2 : Option Bool), w1 = w2 → p1 = p2 →
      (∀ i, k1.getD i false = k2.getD i false) →
      (bs.foldl F (k1, w1, p1)).2.1 = (bs.foldl F (k2, w2, p2)).2.1 ∧
        (bs.foldl F (k1, w1, p1)).2.2 = (bs.foldl F (k2, w2, p2)).2.2 ∧
        ∀ i, (bs.foldl F (k1, w1, p1)).1.getD i false = (bs.foldl F (k2, w2, p2)).1.getD i false := by
    intro bs
    induction bs with
    | nil =>
      intro k1 k2 w1 w2 p1 p2 hw hp hs
      subst hw hp
      exact ⟨rfl, rfl, hs⟩
    | cons b bs ih =>
      intro k1 k2 w1 w2 p1 p2 hw hp hs
      rw [List.foldl_cons, List.foldl_cons]
      obtain ⟨h1, h2, h3⟩ := agree_step F hF k1 k2 w1 w2 p1 p2 b hw hp hs
      exact ih _ _ _ _ _ _ h1 h2 h3
  have hs : ∀ i, ([] : List Bool).getD i false = ([false] : List Bool).getD i false := by
    intro i
    cases i <;> simp
  rw [headD_eq_getD_zero, headD_eq_getD_zero]
  exact (key bits [] [false] w w none none rfl rfl hs).2.2 0

end MPP.Solutions.Pnp270
