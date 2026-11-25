import Mathlib

namespace MPP.Solutions.Pnp180

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

-- the reachability clause of pnp-179
def Reach (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ st.1, ∀ w : ℕ, 1 ≤ w → w ≤ e → (∀ f ∈ st.1, f < e → f < w) →
    Relation.ReflTransGen (fun c a => (a, c) ∈ st.2.2.2) e w

-- stack non-increasing, the top is the time minus one, and the reach clause
def J (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) : Prop :=
  st.1.Pairwise (fun a c => a ≥ c) ∧ (st.1 = [] → st.2.1 = 1) ∧
    (∀ h t, st.1 = h :: t → h + 1 = st.2.1) ∧ Reach st

-- every logged arc goes from an operand below the gate, and every gate is already created;
-- every wire below the time has an interval as its consumption cone
def K (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) : Prop :=
  (∀ q ∈ st.2.2.2, 1 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 < st.2.1) ∧
    (∀ i, i < st.2.1 → ∃ lo, lo ≤ i ∧
      ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ st.2.2.2) i w ↔ (lo ≤ w ∧ w ≤ i))

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

theorem mem_newL (S : List ℕ) (L : List (ℕ × ℕ)) (T : ℕ) (q : ℕ × ℕ)
    (hq : q ∈ ((S.take 2).filter (· != 0)).map (fun u => (u, T)) ++ L) :
    q ∈ L ∨ ∃ u ∈ S.take 2, u ≠ 0 ∧ q = (u, T) := by
  rcases List.mem_append.mp hq with h | h
  · right
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    obtain ⟨hu1, hu2⟩ := List.mem_filter.mp hu
    exact ⟨u, hu1, by simpa using hu2, rfl⟩
  · exact Or.inl h

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

-- no arc is logged at gate i: the cone of i is {i}
theorem rtg_self {L : List (ℕ × ℕ)} {i : ℕ} (hno : ∀ q ∈ L, q.2 ≠ i) {w : ℕ}
    (h : Relation.ReflTransGen (fun c a => (a, c) ∈ L) i w) : w = i := by
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih => exact absurd ih (hno (c, b) hbc)

-- operands are below their gates, so reachable wires are below the start
theorem rtg_le {L : List (ℕ × ℕ)} (hL : ∀ q ∈ L, q.1 < q.2) {i w : ℕ}
    (h : Relation.ReflTransGen (fun c a => (a, c) ∈ L) i w) : w ≤ i := by
  induction h with
  | refl => exact le_refl _
  | @tail b c _ hbc ih =>
    have h1 : c < b := hL (c, b) hbc
    omega

-- for a start below the threshold, paths through the new arcs (gate ≥ T) do not exist
theorem rtg_restrict {L L' : List (ℕ × ℕ)} {T i : ℕ} (hL : ∀ q ∈ L, q.1 < q.2)
    (hnew : ∀ q ∈ L', q ∈ L ∨ T ≤ q.2) (hi : i < T) {w : ℕ}
    (h : Relation.ReflTransGen (fun c a => (a, c) ∈ L') i w) :
    Relation.ReflTransGen (fun c a => (a, c) ∈ L) i w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases hnew (c, b) hbc with h1 | h1
    · exact Relation.ReflTransGen.tail ih h1
    · have hb : b ≤ i := rtg_le hL ih
      have h2 : T ≤ b := h1
      exfalso
      omega

theorem old_cone {L L' : List (ℕ × ℕ)} {T i lo : ℕ} (hL : ∀ q ∈ L, q.1 < q.2)
    (hnew : ∀ q ∈ L', q ∈ L ∨ T ≤ q.2) (hLL' : ∀ q ∈ L, q ∈ L') (hi : i < T)
    (hw : ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L) i w ↔ (lo ≤ w ∧ w ≤ i)) :
    ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L') i w ↔ (lo ≤ w ∧ w ≤ i) := by
  intro w
  exact ⟨fun h => (hw w).1 (rtg_restrict hL hnew hi h),
    fun h => rtg_mono hLL' ((hw w).2 h)⟩

-- a new wire with no arc to it from its operands: its cone is {T}
theorem cone_none {L L' : List (ℕ × ℕ)} {T : ℕ} (hL : ∀ q ∈ L, q.2 < T)
    (hL' : ∀ q ∈ L', q ∈ L) : ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L') T w ↔
      (T ≤ w ∧ w ≤ T) := by
  intro w
  constructor
  · intro h
    have h1 := rtg_self (i := T) (fun q hq => by have := hL q hq; omega) (rtg_mono hL' h)
    omega
  · rintro ⟨h1, h2⟩
    obtain rfl : w = T := by omega
    exact Relation.ReflTransGen.refl

-- a new wire with one operand s1: its cone is [lo1, T]
theorem cone_one {L L' : List (ℕ × ℕ)} {T s1 lo1 : ℕ} (hL : ∀ q ∈ L, q.1 < q.2 ∧ q.2 < T)
    (hs1 : s1 + 1 = T) (hI1 : ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L) s1 w ↔
      (lo1 ≤ w ∧ w ≤ s1))
    (hL' : ∀ q ∈ L', q ∈ L ∨ q = (s1, T)) (hLL' : ∀ q ∈ L, q ∈ L') (harc : (s1, T) ∈ L') :
    ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L') T w ↔ (lo1 ≤ w ∧ w ≤ T) := by
  have hnew : ∀ q ∈ L', q ∈ L ∨ T ≤ q.2 := by
    intro q hq
    rcases hL' q hq with h | h
    · exact Or.inl h
    · subst h
      exact Or.inr le_rfl
  intro w
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h0 | ⟨c, hc, hcw⟩
    · have hlo : lo1 ≤ s1 := ((hI1 s1).1 Relation.ReflTransGen.refl).1
      omega
    · have hc' : c = s1 := by
        rcases hL' (c, T) hc with h1 | h1
        · exfalso
          have h2 : T < T := (hL (c, T) h1).2
          omega
        · exact congrArg Prod.fst h1
      rw [hc'] at hcw
      have h3 := (hI1 w).1 (rtg_restrict (fun q hq => (hL q hq).1) hnew (by omega) hcw)
      omega
  · rintro ⟨h1, h2⟩
    by_cases hwT : w = T
    · rw [hwT]
    · have hws1 : w ≤ s1 := by omega
      have hold : Relation.ReflTransGen (fun c a => (a, c) ∈ L) s1 w := (hI1 w).2 ⟨h1, hws1⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single harc)
        (rtg_mono hLL' hold)

-- a new wire with two operands s1 ≥ s2 ≥ 1: its cone is [min lo1 lo2, T]
theorem cone_two {L L' : List (ℕ × ℕ)} {T s1 s2 lo1 lo2 : ℕ}
    (hL : ∀ q ∈ L, q.1 < q.2 ∧ q.2 < T) (hs1 : s1 + 1 = T) (hs21 : s2 ≤ s1)
    (hI1 : ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L) s1 w ↔ (lo1 ≤ w ∧ w ≤ s1))
    (hI2 : ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L) s2 w ↔ (lo2 ≤ w ∧ w ≤ s2))
    (hlo : lo1 ≤ s2 + 1)
    (hL' : ∀ q ∈ L', q ∈ L ∨ q = (s1, T) ∨ q = (s2, T))
    (hLL' : ∀ q ∈ L, q ∈ L') (harc1 : (s1, T) ∈ L') (harc2 : (s2, T) ∈ L') :
    ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L') T w ↔ (min lo1 lo2 ≤ w ∧ w ≤ T) := by
  have hL2 : ∀ q ∈ L, q.1 < q.2 := fun q hq => (hL q hq).1
  have hnew : ∀ q ∈ L', q ∈ L ∨ T ≤ q.2 := by
    intro q hq
    rcases hL' q hq with h | h | h
    · exact Or.inl h
    · subst h
      exact Or.inr le_rfl
    · subst h
      exact Or.inr (by omega)
  have hlo1 : lo1 ≤ s1 := ((hI1 s1).1 Relation.ReflTransGen.refl).1
  intro w
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h0 | ⟨c, hc, hcw⟩
    · omega
    · rcases hL' (c, T) hc with h1 | h1 | h1
      · exfalso
        have h2 : T < T := (hL (c, T) h1).2
        omega
      · have hc' : c = s1 := congrArg Prod.fst h1
        rw [hc'] at hcw
        have h3 := (hI1 w).1 (rtg_restrict hL2 hnew (by omega) hcw)
        omega
      · have hc' : c = s2 := congrArg Prod.fst h1
        rw [hc'] at hcw
        have h3 := (hI2 w).1 (rtg_restrict hL2 hnew (by omega) hcw)
        omega
  · rintro ⟨h1, h2⟩
    by_cases hwT : w = T
    · rw [hwT]
    · by_cases hA : lo1 ≤ w
      · have hws1 : w ≤ s1 := by omega
        have hold : Relation.ReflTransGen (fun c a => (a, c) ∈ L) s1 w := (hI1 w).2 ⟨hA, hws1⟩
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single harc1)
          (rtg_mono hLL' hold)
      · have hlo2 : lo2 ≤ w := by omega
        have hws2 : w ≤ s2 := by omega
        have hold : Relation.ReflTransGen (fun c a => (a, c) ∈ L) s2 w := (hI2 w).2 ⟨hlo2, hws2⟩
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single harc2)
          (rtg_mono hLL' hold)

theorem init_K : K ([], 1, none, []) := by
  unfold K
  refine ⟨fun q hq => by simp at hq, fun i hi => ?_⟩
  have hi0 : i = 0 := by
    simp at hi
    omega
  refine ⟨0, Nat.zero_le _, fun w => ?_⟩
  constructor
  · intro h
    have := rtg_self (i := i) (fun q hq => by simp at hq) h
    omega
  · rintro ⟨h1, h2⟩
    obtain rfl : w = i := by omega
    exact Relation.ReflTransGen.refl

-- a new wire with no operand: nothing new is logged at its gate, its cone is {T}
theorem K_noarc {L L' : List (ℕ × ℕ)} {T : ℕ}
    (hA : ∀ q ∈ L, 1 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 < T)
    (hB : ∀ i, i < T → ∃ lo, lo ≤ i ∧
      ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L) i w ↔ (lo ≤ w ∧ w ≤ i))
    (hL' : ∀ q ∈ L', q ∈ L) (hLL' : ∀ q ∈ L, q ∈ L') :
    (∀ q ∈ L', 1 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 < T + 1) ∧
      (∀ i, i < T + 1 → ∃ lo, lo ≤ i ∧
        ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L') i w ↔ (lo ≤ w ∧ w ≤ i)) := by
  refine ⟨fun q hq => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hA q (hL' q hq)
    exact ⟨h1, h2, by omega⟩
  · rcases Nat.lt_or_ge i T with hiT | hiT
    · obtain ⟨lo, hlo, hw⟩ := hB i hiT
      exact ⟨lo, hlo, old_cone (fun q hq => (hA q hq).2.1) (fun q hq => Or.inl (hL' q hq))
        hLL' hiT hw⟩
    · have hiT' : i = T := by omega
      refine ⟨T, by omega, ?_⟩
      rw [hiT']
      exact cone_none (fun q hq => (hA q hq).2.2) hL'

-- a new wire with one operand s1 = T - 1 (the only arc into T is (s1, T))
theorem K_one {L L' : List (ℕ × ℕ)} {T s1 : ℕ}
    (hA : ∀ q ∈ L, 1 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 < T) (hs1 : s1 + 1 = T) (hs0 : 1 ≤ s1)
    (hB : ∀ i, i < T → ∃ lo, lo ≤ i ∧
      ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L) i w ↔ (lo ≤ w ∧ w ≤ i))
    (hL' : ∀ q ∈ L', q ∈ L ∨ q = (s1, T)) (hLL' : ∀ q ∈ L, q ∈ L')
    (harc : (s1, T) ∈ L') :
    (∀ q ∈ L', 1 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 < T + 1) ∧
      (∀ i, i < T + 1 → ∃ lo, lo ≤ i ∧
        ∀ w, Relation.ReflTransGen (fun c a => (a, c) ∈ L') i w ↔ (lo ≤ w ∧ w ≤ i)) := by
  obtain ⟨lo1, hlo1, hI1⟩ := hB s1 (by omega)
  have hnew : ∀ q ∈ L', q ∈ L ∨ T ≤ q.2 := by
    intro q hq
    rcases hL' q hq with h | h
    · exact Or.inl h
    · subst h
      exact Or.inr le_rfl
  refine ⟨fun q hq => ?_, fun i hi => ?_⟩
  · rcases hL' q hq with h | h
    · obtain ⟨h1, h2, h3⟩ := hA q h
      exact ⟨h1, h2, by omega⟩
    · subst h
      show 1 ≤ s1 ∧ s1 < T ∧ T < T + 1
      omega
  · rcases Nat.lt_or_ge i T with hiT | hiT
    · obtain ⟨lo, hlo, hw⟩ := hB i hiT
      exact ⟨lo, hlo, old_cone (fun q hq => (hA q hq).2.1) hnew hLL' hiT hw⟩
    · have hiT' : i = T := by omega
      refine ⟨lo1, by omega, ?_⟩
      rw [hiT']
      exact cone_one (fun q hq => ⟨(hA q hq).2.1, (hA q hq).2.2⟩) hs1 hI1 hL' hLL' harc

theorem step_K (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) (hJ : J st) (hK : K st) :
    K (stepF st b) := by
  obtain ⟨S, T, p, L⟩ := st
  unfold J Reach at hJ
  unfold K at hK ⊢
  obtain ⟨hP, hE, hH, hR⟩ := hJ
  obtain ⟨hA, hB⟩ := hK
  dsimp only at hP hE hH hR hA hB ⊢
  cases p with
  | none =>
    simp only [stepF]
    exact ⟨hA, hB⟩
  | some a =>
    cases a <;> cases b
    · -- leaf: the new wire T has no arcs yet
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun q hq => ?_, fun i hi => ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hA q hq
        exact ⟨h1, h2, by omega⟩
      · rcases Nat.lt_or_ge i T with hiT | hiT
        · obtain ⟨lo, hlo, hw⟩ := hB i hiT
          exact ⟨lo, hlo, hw⟩
        · have hiT' : i = T := by omega
          refine ⟨T, by omega, ?_⟩
          rw [hiT']
          exact cone_none (fun q hq => (hA q hq).2.2) (fun q hq => hq)
    · -- copy: the time and the logged arcs do not change
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hA, hB⟩
    · -- no-op
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hA, hB⟩
    · -- NAND
      simp only [stepF, ↓reduceIte]
      cases S with
      | nil =>
        refine K_noarc hA hB (fun q hq => ?_) (fun q hq => List.mem_append_right _ hq)
        rcases mem_newL _ L T q hq with h | ⟨u, hu, -⟩
        · exact h
        · simp at hu
      | cons s1 r =>
        have hs1 : s1 + 1 = T := hH s1 r rfl
        cases r with
        | nil =>
          by_cases hs10 : s1 = 0
          · refine K_noarc hA hB (fun q hq => ?_) (fun q hq => List.mem_append_right _ hq)
            rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, -⟩
            · exact h
            · simp at hu
              omega
          · refine K_one hA hs1 (by omega) hB (fun q hq => ?_)
              (fun q hq => List.mem_append_right _ hq) (arc_mem [s1] L T s1 (by simp) (by omega))
            rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, hqu⟩
            · exact Or.inl h
            · simp at hu
              right
              rw [hqu, hu]
        | cons s2 r' =>
          have hs21 : s2 ≤ s1 := (List.pairwise_cons.mp hP).1 s2 (by simp)
          have hr2 : ∀ b ∈ r', b ≤ s2 := (List.pairwise_cons.mp (List.pairwise_cons.mp hP).2).1
          have htake : (s1 :: s2 :: r').take 2 = [s1, s2] := rfl
          by_cases hs2 : s2 = 0
          · by_cases hs10 : s1 = 0
            · refine K_noarc hA hB (fun q hq => ?_) (fun q hq => List.mem_append_right _ hq)
              rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, -⟩
              · exact h
              · rw [htake] at hu
                simp at hu
                omega
            · refine K_one hA hs1 (by omega) hB (fun q hq => ?_)
                (fun q hq => List.mem_append_right _ hq)
                (arc_mem (s1 :: s2 :: r') L T s1 (by simp) (by omega))
              rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, hqu⟩
              · exact Or.inl h
              · rw [htake] at hu
                simp at hu
                rcases hu with hu | hu
                · right
                  rw [hqu, hu]
                · omega
          · have hs2' : 1 ≤ s2 := by omega
            obtain ⟨lo1, hlo1, hI1⟩ := hB s1 (by omega)
            obtain ⟨lo2, hlo2, hI2⟩ := hB s2 (by omega)
            have hlo : lo1 ≤ s2 + 1 := by
              rcases Nat.lt_or_ge s2 s1 with hlt | hge
              · have hR1 := hR s1 (by simp) (s2 + 1) (by omega) (by omega)
                  (fun f hf _ => by
                    rcases List.mem_cons.mp hf with hf1 | hf'
                    · omega
                    · rcases List.mem_cons.mp hf' with hf2 | hf''
                      · omega
                      · have := hr2 f hf''
                        omega)
                exact ((hI1 (s2 + 1)).1 hR1).1
              · omega
            refine ⟨fun q hq => ?_, fun i hi => ?_⟩
            · rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, hqu⟩
              · obtain ⟨h1, h2, h3⟩ := hA q h
                exact ⟨h1, h2, by omega⟩
              · rw [htake] at hu
                simp at hu
                subst hqu
                show 1 ≤ u ∧ u < T ∧ T < T + 1
                rcases hu with rfl | rfl
                · omega
                · omega
            · rcases Nat.lt_or_ge i T with hiT | hiT
              · obtain ⟨lo, hlo', hw⟩ := hB i hiT
                refine ⟨lo, hlo', old_cone (fun q hq => (hA q hq).2.1) (fun q hq => ?_)
                  (fun q hq => List.mem_append_right _ hq) hiT hw⟩
                rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, hqu⟩
                · exact Or.inl h
                · exact Or.inr (by rw [hqu])
              · have hiT' : i = T := by omega
                refine ⟨min lo1 lo2, by omega, ?_⟩
                rw [hiT']
                refine cone_two (fun q hq => ⟨(hA q hq).2.1, (hA q hq).2.2⟩) hs1 hs21 hI1 hI2 hlo
                  (fun q hq => ?_) (fun q hq => List.mem_append_right _ hq)
                  (arc_mem (s1 :: s2 :: r') L T s1 (by simp) (by omega))
                  (arc_mem (s1 :: s2 :: r') L T s2 (by simp) (by omega))
                rcases mem_newL _ L T q hq with h | ⟨u, hu, hu0, hqu⟩
                · exact Or.inl h
                · rw [htake] at hu
                  simp at hu
                  rcases hu with hu | hu
                  · right; left; rw [hqu, hu]
                  · right; right; rw [hqu, hu]

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
    ∀ i w w' : ℕ, 1 ≤ i → i < s.2.1 →
      Relation.ReflTransGen (fun c a => (a, c) ∈ s.2.2.2) i w → w ≤ w' → w' ≤ i →
        Relation.ReflTransGen (fun c a => (a, c) ∈ s.2.2.2) i w' := by
  intro x s hs
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      J st → K st → J (x.foldl stepF st) ∧ K (x.foldl stepF st) := by
    intro x
    induction x with
    | nil => intro st hJ hK; exact ⟨hJ, hK⟩
    | cons b x ih => intro st hJ hK; exact ih _ (step_J st b hJ) (step_K st b hJ hK)
  have hI := key x _ init_J init_K
  rw [← hs]
  intro i w w' hi1 hiT hr hw1 hw2
  have hK := hI.2
  unfold K at hK
  obtain ⟨lo, hlo, hw⟩ := hK.2 i hiT
  exact (hw w').2 ⟨le_trans ((hw w).1 hr).1 hw1, hw2⟩

end MPP.Solutions.Pnp180
