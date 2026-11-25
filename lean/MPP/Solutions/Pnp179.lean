import Mathlib

namespace MPP.Solutions.Pnp179

def stepF (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) :
    List ℕ × ℕ × Option Bool × List (ℕ × ℕ) :=
  match st.2.2.1 with
  | none => (st.1, st.2.1, some b, st.2.2.2)
  | some a =>
    if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
        ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
      else (st.1, st.2.1, none, st.2.2.2))
    else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
      else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))

-- the reachability clause of the claim, read off the final logged arcs
def Reach (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ st.1, ∀ w : ℕ, 1 ≤ w → w ≤ e → (∀ f ∈ st.1, f < e → f < w) →
    Relation.ReflTransGen (fun c a => (a, c) ∈ st.2.2.2) e w

-- stack non-increasing, the top is the time minus one, and the reach clause
def J (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) : Prop :=
  st.1.Pairwise (fun a c => a ≥ c) ∧ (st.1 = [] → st.2.1 = 1) ∧
    (∀ h t, st.1 = h :: t → h + 1 = st.2.1) ∧ Reach st

theorem headD_ge (S : List ℕ) (hS : S.Pairwise (fun a c => a ≥ c)) :
    ∀ e ∈ S, S.headD 0 ≥ e := by
  intro e he
  cases S with
  | nil => simp at he
  | cons x t =>
    rcases List.mem_cons.mp he with rfl | he'
    · simp
    · exact (List.pairwise_cons.mp hS).1 e he'

theorem rtg_mono {L L' : List (ℕ × ℕ)} (hL : ∀ q ∈ L, q ∈ L') {e w : ℕ}
    (h : Relation.ReflTransGen (fun c a => (a, c) ∈ L) e w) :
    Relation.ReflTransGen (fun c a => (a, c) ∈ L') e w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (hL _ hbc)

theorem arc_mem (S : List ℕ) (L : List (ℕ × ℕ)) (T u : ℕ) (hu : u ∈ S.take 2) (hne : u ≠ 0) :
    (u, T) ∈ ((S.take 2).filter (· != 0)).map (fun u => (u, T)) ++ L := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, by simpa using hne⟩, rfl⟩

theorem step_J (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) (h : J st) :
    J (stepF st b) := by
  obtain ⟨S, T, p, L⟩ := st
  unfold J Reach at h ⊢
  obtain ⟨hP, hE, hH, hR⟩ := h
  dsimp only at hP hE hH hR ⊢
  cases p with
  | none =>
    simp only [stepF]
    exact ⟨hP, hE, hH, hR⟩
  | some a =>
    cases a <;> cases b
    · -- leaf: push the time T, which is above every entry
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      have hSlt : ∀ e ∈ S, e < T := by
        intro e he
        cases S with
        | nil => simp at he
        | cons h' t =>
          have h1 : e ≤ h' := by
            have := headD_ge (h' :: t) hP e he
            simpa using this
          have h2 : h' + 1 = T := hH h' t rfl
          omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun e he => (hSlt e he).le, hP⟩
      · intro h0
        exact absurd h0 (List.cons_ne_nil _ _)
      · intro h' t' hh'
        obtain ⟨rfl, -⟩ := List.cons.inj hh'
        omega
      · intro e he w hw1 hwe hcond
        rcases List.mem_cons.mp he with he1 | he'
        · have hwT : w = T := by
            cases S with
            | nil =>
              have hT := hE rfl
              omega
            | cons h' t =>
              have h1 : h' + 1 = T := hH h' t rfl
              have h2 : h' < w := hcond h' (by simp) (by omega)
              omega
          rw [he1, hwT]
        · refine hR e he' w hw1 hwe ?_
          intro f hf hfe
          exact hcond f (List.mem_cons_of_mem _ hf) hfe
    · -- copy: push the top again (0 on an empty stack)
      cases S with
      | nil =>
        have hT : T = 1 := hE rfl
        simp only [stepF, Bool.false_eq_true, ↓reduceIte, List.headD_nil]
        refine ⟨by simp, fun h0 => absurd h0 (by simp), fun h' t' hh' => ?_,
          fun e he w hw1 hwe _ => ?_⟩
        · obtain ⟨rfl, -⟩ := List.cons.inj hh'
          omega
        · have he0 : e = 0 := by simpa using he
          exfalso
          omega
      | cons h t =>
        have hh : h + 1 = T := hH h t rfl
        have hle : ∀ e ∈ h :: t, e ≤ h := fun e he => by
          have := headD_ge (h :: t) hP e he
          simpa using this
        simp only [stepF, Bool.false_eq_true, ↓reduceIte, List.headD_cons]
        refine ⟨List.pairwise_cons.mpr ⟨fun e he => hle e he, hP⟩,
          fun h0 => absurd h0 (by simp), fun h' t' hh' => ?_, fun e he w hw1 hwe hcond => ?_⟩
        · obtain ⟨rfl, -⟩ := List.cons.inj hh'
          exact hh
        · have he2 : e ∈ h :: t := by
            rcases List.mem_cons.mp he with he1 | he1
            · rw [he1]
              simp
            · exact he1
          exact hR e he2 w hw1 hwe (fun f hf hfe => hcond f (List.mem_cons_of_mem _ hf) hfe)
    · -- no-op
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hP, hE, hH, hR⟩
    · -- NAND: pop two, push the time T, log the popped nonzero ids at T
      simp only [stepF, ↓reduceIte]
      cases S with
      | nil =>
        have hT : T = 1 := hE rfl
        refine ⟨by simp, fun h0 => absurd h0 (by simp), fun h' t' hh' => ?_, fun e he w hw1 hwe _ => ?_⟩
        · obtain ⟨rfl, -⟩ := List.cons.inj hh'
          omega
        · have he1 : e = T := by simpa using he
          have hwe' : w = e := by omega
          rw [hwe']
      | cons s1 r =>
        have hs1 : s1 + 1 = T := hH s1 r rfl
        cases r with
        | nil =>
          refine ⟨by simp, fun h0 => absurd h0 (by simp), fun h' t' hh' => ?_,
            fun e he w hw1 hwe hcond => ?_⟩
          · obtain ⟨rfl, -⟩ := List.cons.inj hh'
            omega
          · have he1 : e = T := by simpa using he
            by_cases hwT : w = T
            · rw [he1, hwT]
            · have hold : Relation.ReflTransGen (fun c a => (a, c) ∈ L) s1 w :=
                hR s1 (by simp) w hw1 (by omega) (fun f hf hfe => by
                  simp only [List.mem_singleton] at hf
                  omega)
              rw [he1]
              exact Relation.ReflTransGen.trans
                (Relation.ReflTransGen.single (arc_mem [s1] L T s1 (by simp) (by omega)))
                (rtg_mono (fun q hq => List.mem_append_right _ hq) hold)
        | cons s2 r' =>
          have hA := List.pairwise_cons.mp hP
          have hB := List.pairwise_cons.mp hA.2
          have hr_lt : ∀ f ∈ r', f < T := fun f hf => by
            have := hA.1 f (List.mem_cons_of_mem _ hf)
            omega
          refine ⟨?_, fun h0 => absurd h0 (by simp), fun h' t' hh' => ?_,
            fun e he w hw1 hwe hcond => ?_⟩
          · exact List.pairwise_cons.mpr ⟨fun e he => (hr_lt e he).le, hB.2⟩
          · obtain ⟨rfl, -⟩ := List.cons.inj hh'
            omega
          · rcases List.mem_cons.mp he with he1 | he'
            · by_cases hwT : w = T
              · rw [he1, hwT]
              · rw [he1]
                by_cases hs2w : s2 < w
                · have hold : Relation.ReflTransGen (fun c a => (a, c) ∈ L) s1 w :=
                    hR s1 (by simp) w hw1 (by omega) (fun f hf hfe => by
                      rcases List.mem_cons.mp hf with hf1 | hf'
                      · omega
                      · rcases List.mem_cons.mp hf' with hf2 | hf''
                        · omega
                        · exact hcond f (List.mem_cons_of_mem _ hf'') (by
                            have := hr_lt f hf''
                            omega))
                  exact Relation.ReflTransGen.trans
                    (Relation.ReflTransGen.single
                      (arc_mem (s1 :: s2 :: r') L T s1 (by simp) (by omega)))
                    (rtg_mono (fun q hq => List.mem_append_right _ hq) hold)
                · have hold : Relation.ReflTransGen (fun c a => (a, c) ∈ L) s2 w :=
                    hR s2 (by simp) w hw1 (by omega) (fun f hf hfe => by
                      rcases List.mem_cons.mp hf with hf1 | hf'
                      · have := hA.1 s2 (by simp)
                        omega
                      · rcases List.mem_cons.mp hf' with hf2 | hf''
                        · omega
                        · exact hcond f (List.mem_cons_of_mem _ hf'') (by
                            have := hr_lt f hf''
                            omega))
                  exact Relation.ReflTransGen.trans
                    (Relation.ReflTransGen.single
                      (arc_mem (s1 :: s2 :: r') L T s2 (by simp) (by omega)))
                    (rtg_mono (fun q hq => List.mem_append_right _ hq) hold)
            · refine rtg_mono (fun q hq => List.mem_append_right _ hq)
                (hR e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he')) w hw1 hwe ?_)
              intro f hf hfe
              rcases List.mem_cons.mp hf with hf1 | hf'
              · have := hA.1 e (List.mem_cons_of_mem _ he')
                omega
              · rcases List.mem_cons.mp hf' with hf2 | hf''
                · have := hB.1 e he'
                  omega
                · exact hcond f (List.mem_cons_of_mem _ hf'') hfe

theorem init_J : J ([], 1, none, []) := by
  unfold J Reach
  refine ⟨List.Pairwise.nil, fun _ => rfl, fun h t hh => by simp at hh, fun e he => by simp at he⟩

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
    ∀ e ∈ s.1, ∀ w : ℕ, 1 ≤ w → w ≤ e → (∀ f ∈ s.1, f < e → f < w) →
      Relation.ReflTransGen (fun c a => (a, c) ∈ s.2.2.2) e w := by
  intro x s hs
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      J st → J (x.foldl stepF st) := by
    intro x
    induction x with
    | nil => intro st h; exact h
    | cons b x ih => intro st h; exact ih _ (step_J st b h)
  have hI := key x _ init_J
  rw [← hs]
  unfold J Reach at hI
  exact hI.2.2.2

end MPP.Solutions.Pnp179
