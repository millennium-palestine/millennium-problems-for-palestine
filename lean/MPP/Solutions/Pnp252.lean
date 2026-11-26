import Mathlib
import MPP.Solutions.Pnp200
import MPP.Solutions.Pnp213

namespace MPP.Solutions.Pnp252

def Hh (r : Bool × Bool) : ℤ := if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1

def stepF (st : List Bool × List Bool × Option Bool) (b : Bool) :
    List Bool × List Bool × Option Bool :=
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))

def seg (s : ℕ → Bool × Bool) (i j : ℕ) : List (Bool × Bool) :=
  (List.range (j - i)).map (fun k => s (i + k))

abbrev Bal (q : List (Bool × Bool)) : Prop :=
  (∀ j, j ≤ q.length → 0 ≤ ((q.map Hh).take j).sum) ∧ (q.map Hh).sum = 0

abbrev Run (q : List (Bool × Bool)) (p : Bool × Bool) : Prop :=
  ∃ w : List Bool, w.length = q.countP (fun x => !x.1 && !x.2) ∧ ∃ w' : List Bool,
    (q.flatMap fun r => [r.1, r.2]).foldl stepF (p.1 :: [], w, none) = (p.2 :: [], w', none)

abbrev Tab (s : ℕ → Bool × Bool) (i j : ℕ) (p : Bool × Bool) : Prop :=
  Bal (seg s i j) ∧ Run (seg s i j) p

theorem seg_zero (s : ℕ → Bool × Bool) (i : ℕ) : seg s i i = [] := by
  simp [seg]

theorem seg_length (s : ℕ → Bool × Bool) (i j : ℕ) : (seg s i j).length = j - i := by
  simp [seg]

theorem seg_succ (s : ℕ → Bool × Bool) {i j : ℕ} (h : i ≤ j) :
    seg s i (j + 1) = seg s i j ++ [s j] := by
  unfold seg
  have h1 : j + 1 - i = (j - i) + 1 := by omega
  have h2 : i + (j - i) = j := by omega
  rw [h1, List.range_succ, List.map_append]
  simp [h2]

theorem seg_split (s : ℕ → Bool × Bool) {i k j : ℕ} (h1 : i ≤ k) (h2 : k ≤ j) :
    seg s i k ++ seg s k j = seg s i j := by
  induction j, h2 using Nat.le_induction with
  | base => simp [seg_zero]
  | succ j hkj ih =>
    rw [seg_succ s hkj, ← List.append_assoc, ih, seg_succ s (le_trans h1 hkj)]

theorem seg_cons (s : ℕ → Bool × Bool) {i j : ℕ} (h : i + 2 ≤ j) :
    seg s i j = s i :: (seg s (i + 1) (j - 1) ++ [s (j - 1)]) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hm : m + 1 - 1 = m := by omega
  rw [hm, ← seg_split s (show i ≤ i + 1 by omega) (show i + 1 ≤ m + 1 by omega),
    seg_succ s (show i + 1 ≤ m by omega), seg_succ s (le_refl i), seg_zero]
  simp

theorem bal_nil : Bal [] :=
  ⟨fun j hj => by simp at hj; subst hj; simp, by simp⟩

theorem bal_single (x : Bool × Bool) : Bal [x] ↔ x = (true, false) := by
  constructor
  · rintro ⟨-, h2⟩
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> simp [Hh] at h2 ⊢
  · rintro rfl
    refine ⟨fun j hj => ?_, by simp [Hh]⟩
    have hj' : j ≤ 1 := by simpa using hj
    interval_cases j <;> simp [Hh]

theorem bal_append {p s : List (Bool × Bool)} (hp : Bal p) (hs : Bal s) : Bal (p ++ s) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · intro j hj
    rw [List.length_append] at hj
    rw [List.map_append, List.take_append, List.sum_append, List.length_map]
    rcases Nat.le_total j p.length with h | h
    · rw [show j - p.length = 0 by omega, List.take_zero, List.sum_nil, add_zero]
      exact hp1 j h
    · rw [List.take_of_length_le (show (p.map Hh).length ≤ j by simp; omega), hp2, zero_add]
      exact hs1 (j - p.length) (by omega)
  · rw [List.map_append, List.sum_append, hp2, hs2, add_zero]

-- the primitive block is balanced (pnp-251, with the height Hh)
theorem bal_prim (a c : Bool × Bool) (mid : List (Bool × Bool)) (ha : a.1 = false)
    (hc : c = (true, true)) (hsum : (mid.map Hh).sum = 0)
    (hpre : ∀ j, j ≤ mid.length → 0 ≤ ((mid.map Hh).take j).sum) :
    Bal (a :: (mid ++ [c])) := by
  subst hc
  have hH2 : Hh (true, true) = -1 := by simp [Hh]
  have hA : Hh a = 1 := by
    obtain ⟨x, y⟩ := a
    simp only at ha
    subst ha
    simp [Hh]
  have hmap : (a :: (mid ++ [((true, true) : Bool × Bool)])).map Hh = 1 :: ((mid.map Hh) ++ [-1]) := by
    simp [hA, hH2]
  unfold Bal
  rw [hmap]
  constructor
  · intro j hj
    have hlen : (a :: (mid ++ [((true, true) : Bool × Bool)])).length = mid.length + 2 := by
      simp only [List.length_cons, List.length_append, List.length_nil]
    rw [hlen] at hj
    rcases j with _ | k
    · simp
    · rw [List.take_succ_cons, List.sum_cons]
      rcases Nat.lt_or_ge k (mid.length + 1) with hk | hk
      · have hk2 : k ≤ (mid.map Hh).length := by simp; omega
        rw [List.take_append_of_le_length hk2]
        have := hpre k (by omega)
        omega
      · have hk' : k = mid.length + 1 := by omega
        subst hk'
        rw [List.take_of_length_le (by simp)]
        simp [hsum]
  · simp [hsum]

theorem tail_tr (q : List (Bool × Bool)) (h1 : ∀ j, j ≤ q.length → 0 ≤ ((q.map Hh).take j).sum)
    (h2 : (q.map Hh).sum = 0) (r r' : List Bool) (u g : Bool) (w w' : List Bool)
    (h : (q.flatMap fun x => [x.1, x.2]).foldl stepF (u :: r, w, none) = (g :: r, w', none)) :
    (q.flatMap fun x => [x.1, x.2]).foldl stepF (u :: r', w, none) = (g :: r', w', none) :=
  MPP.Solutions.Pnp200.main q h1 h2 r r' w w' u g h

theorem run_nil (p : Bool × Bool) : Run [] p ↔ p.1 = p.2 := by
  constructor
  · rintro ⟨w, -, w', h⟩
    simp at h
    exact h.1
  · intro h
    exact ⟨[], by simp, [], by simp [h]⟩

theorem run_leaf (p : Bool × Bool) : Run [(true, false)] p ↔ p.1 = p.2 := by
  constructor
  · rintro ⟨w, -, w', h⟩
    simp [stepF] at h
    exact h.1
  · intro h
    exact ⟨[], by simp, [], by simp [stepF, h]⟩

theorem tab_zero (s : ℕ → Bool × Bool) (i : ℕ) (p : Bool × Bool) : Tab s i i p ↔ p.1 = p.2 := by
  simp only [Tab, seg_zero]
  constructor
  · rintro ⟨-, h⟩
    exact (run_nil p).1 h
  · intro h
    exact ⟨bal_nil, (run_nil p).2 h⟩

theorem tab_one (s : ℕ → Bool × Bool) (i : ℕ) (p : Bool × Bool) :
    Tab s i (i + 1) p ↔ s i = (true, false) ∧ p.1 = p.2 := by
  have hs : seg s i (i + 1) = [s i] := by
    rw [seg_succ s (le_refl i), seg_zero]
    simp
  simp only [Tab, hs]
  constructor
  · rintro ⟨hb, hr⟩
    have hx := (bal_single (s i)).1 hb
    rw [hx] at hr
    exact ⟨hx, (run_leaf p).1 hr⟩
  · rintro ⟨hx, hp⟩
    refine ⟨(bal_single (s i)).2 hx, ?_⟩
    rw [hx]
    exact (run_leaf p).2 hp

-- the recurrence of pnp-250 for the balanced-block table
theorem tab_rec (s : ℕ → Bool × Bool) {i j : ℕ} (h : i + 2 ≤ j) (p : Bool × Bool) :
    Tab s i j p ↔
      (((s i).1 = false ∧ ∃ u : Bool, ((s i).2 = true → u = p.1) ∧ s (j - 1) = (true, true) ∧
          Bal (seg s (i + 1) (j - 1)) ∧ ∃ g' : Bool, Tab s (i + 1) (j - 1) (u, g') ∧ p.2 = !(g' && p.1)) ∨
       (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, Tab s i k (p.1, g1) ∧ Tab s k j (g1, p.2))) := by
  have hq := seg_cons s h
  have hlen : 0 < (seg s i j).length := by rw [seg_length]; omega
  have P213 := MPP.Solutions.Pnp213.main stepF rfl Hh rfl
  constructor
  · rintro ⟨hBal, hRun⟩
    have key := (P213 (seg s i j) hlen hBal.1 hBal.2 p.1 p.2 []).1 hRun
    rcases key with h1 | h2 | h3
    · exfalso
      have := congrArg List.length h1.1
      rw [seg_length] at this
      simp at this
      omega
    · obtain ⟨a, c, mid, hqa, ha1, hc, hmsum, hmpre, u, hu, g', ⟨w1, hw1, w2, hw2⟩, hg⟩ := h2
      have hh : s i :: (seg s (i + 1) (j - 1) ++ [s (j - 1)]) = a :: (mid ++ [c]) := hq.symm.trans hqa
      rw [List.cons.injEq] at hh
      obtain ⟨hia, hm⟩ := hh
      obtain ⟨hmid, hcc⟩ := List.append_inj' hm (by simp)
      have hc' : s (j - 1) = c := by simpa using hcc
      subst hmid
      subst hc'
      subst hia
      exact Or.inl ⟨ha1, u, hu, hc, ⟨hmpre, hmsum⟩, g', ⟨⟨hmpre, hmsum⟩, w1, hw1, w2,
        tail_tr _ hmpre hmsum [p.1] [] u g' w1 w2 hw2⟩, hg⟩
    · obtain ⟨p', s', hqps, hp'pos, hs'pos, hp'pre, hp'sum, hs'pre, hs'sum, g1,
        ⟨w, hw, w', hw'⟩, ⟨w3, hw3, w3', hw3'⟩⟩ := h3
      have hl : j - i = p'.length + s'.length := by
        have := congrArg List.length hqps
        rw [seg_length, List.length_append] at this
        exact this
      have hk : seg s i (i + p'.length) ++ seg s (i + p'.length) j = p' ++ s' := by
        rw [seg_split s (show i ≤ i + p'.length by omega) (show i + p'.length ≤ j by omega), hqps]
      obtain ⟨hk1, hk2⟩ := List.append_inj hk (by rw [seg_length]; omega)
      have hs'len : s'.length = j - (i + p'.length) := by
        rw [← hk2, seg_length]
      refine Or.inr ⟨i + p'.length, by omega, by omega, g1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [hk1]; exact ⟨hp'pre, hp'sum⟩
      · rw [hk1]; exact ⟨w, hw, w', hw'⟩
      · rw [hk2]; exact ⟨hs'pre, hs'sum⟩
      · rw [hk2]; exact ⟨w3, hw3, w3', hw3'⟩
  · rintro (⟨ha1, u, hu, hc, hmbal, g', htab, hg⟩ | ⟨k, hik, hkj, g1, htab1, htab2⟩)
    · obtain ⟨w1, hw1, w2, hw2⟩ := htab.2
      have hT := tail_tr (seg s (i + 1) (j - 1)) hmbal.1 hmbal.2 [] [p.1] u g' w1 w2 hw2
      have hBal : Bal (seg s i j) := by
        rw [hq]
        exact bal_prim (s i) (s (j - 1)) (seg s (i + 1) (j - 1)) ha1 hc hmbal.2 hmbal.1
      have hRun := (P213 (seg s i j) hlen hBal.1 hBal.2 p.1 p.2 []).2
        (Or.inr (Or.inl ⟨s i, s (j - 1), seg s (i + 1) (j - 1), hq, ha1, hc, hmbal.2, hmbal.1,
          u, hu, g', ⟨w1, hw1, w2, hT⟩, hg⟩))
      exact ⟨hBal, hRun⟩
    · have hsplit := seg_split s (le_of_lt hik) (le_of_lt hkj)
      have hBal : Bal (seg s i j) := by
        rw [← hsplit]
        exact bal_append htab1.1 htab2.1
      have hRun := (P213 (seg s i j) hlen hBal.1 hBal.2 p.1 p.2 []).2
        (Or.inr (Or.inr ⟨seg s i k, seg s k j, hsplit.symm, by rw [seg_length]; omega,
          by rw [seg_length]; omega, htab1.1.1, htab1.1.2, htab2.1.1, htab2.1.2,
          g1, htab1.2, htab2.2⟩))
      exact ⟨hBal, hRun⟩


theorem main : ∀ (s : ℕ → Bool × Bool) (H : Bool × Bool → ℤ) (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool) (Q : ℕ → ℕ → List (Bool × Bool)) (X : ℕ → ℕ → Bool × Bool → Prop),
  H = (fun r => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) →
  F = (fun st b => match st.2.2 with | none => (st.1, st.2.1, some b) | some a => if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none) else (st.1, st.2.1, none)) else (if b then (st.1.headD false :: st.1, st.2.1, none) else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
  (∀ i j, Q i j = (List.range (j - i)).map fun m => s (i + m)) →
  (∀ i j p, X i j p ↔ ((((∀ k, k ≤ (Q i j).length → 0 ≤ (((Q i j).map H).take k).sum) ∧ ((Q i j).map H).sum = 0) ∧ ∃ w : List Bool, w.length = (Q i j).countP (fun x => !x.1 && !x.2) ∧ ∃ w' : List Bool, ((Q i j).flatMap fun r => [r.1, r.2]).foldl F (p.1 :: [], w, none) = (p.2 :: [], w', none)))) →
  (∀ i p, X i i p ↔ p.1 = p.2) ∧ (∀ i p, X i (i + 1) p ↔ s i = (true, false) ∧ p.1 = p.2) ∧
  (∀ i j p, i + 2 ≤ j → (X i j p ↔ ((((s i).1 = false ∧ ∃ u : Bool, ((s i).2 = true → u = p.1) ∧ s (j - 1) = (true, true) ∧ (((∀ k, k ≤ (Q (i + 1) (j - 1)).length → 0 ≤ (((Q (i + 1) (j - 1)).map H).take k).sum) ∧ ((Q (i + 1) (j - 1)).map H).sum = 0) ∧ ∃ g' : Bool, X (i + 1) (j - 1) (u, g') ∧ p.2 = !(g' && p.1))) ∨ (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, X i k (p.1, g1) ∧ X k j (g1, p.2)))))) := by
  intro s H F Q X hH hF hQ hX
  subst hH hF
  have hXT : ∀ i j p, X i j p ↔ Tab s i j p := by
    intro i j p
    rw [hX i j p, hQ i j]
    exact Iff.rfl
  refine ⟨fun i p => ?_, fun i p => ?_, fun i j p hij => ?_⟩
  · rw [hXT]
    exact tab_zero s i p
  · rw [hXT]
    exact tab_one s i p
  · rw [hXT]
    simp only [hXT, hQ]
    exact tab_rec s hij p

end MPP.Solutions.Pnp252
