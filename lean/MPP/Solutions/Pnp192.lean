import Mathlib
import MPP.Solutions.Pnp175

namespace MPP.Solutions.Pnp192

/-- The height step of a pair: -1 for a NAND pair, 0 for a no-op, +1 for a leaf or a copy. -/
def stepZ (q : Bool × Bool) : ℤ := if q.1 && q.2 then -1 else if q.1 then 0 else 1

/-- The first-return lemma (pnp-191), proved here as a helper. -/
theorem zero_first_return (d : List ℤ) (hpos : 0 < d.length)
    (hnn : ∀ j ≤ d.length, 0 ≤ (d.take j).sum) (hsum0 : d.sum = 0) :
    ∃ m, 0 < m ∧ m ≤ d.length ∧ (d.take m).sum = 0 ∧ ∀ j, 0 < j → j < m → 0 < (d.take j).sum := by
  classical
  have hex : ∃ m, 0 < m ∧ (d.take m).sum = 0 :=
    ⟨d.length, hpos, by rw [List.take_length]; exact hsum0⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ d.length :=
    Nat.find_min' hex ⟨hpos, by rw [List.take_length]; exact hsum0⟩
  refine ⟨Nat.find hex, hspec.1, hle, hspec.2, fun j hj1 hj2 => ?_⟩
  have hnz : (d.take j).sum ≠ 0 := fun h => Nat.find_min hex hj2 ⟨hj1, h⟩
  have h0 := hnn j (by omega)
  omega

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool) (run : List (Bool × Bool) → List Bool),
    (∀ p : List (Bool × Bool), run p = ((p.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1) →
    ps.countP (fun q => q.1 && q.2) + 1 ≤ s.length →
    0 < ps.length →
    (∀ j ≤ ps.length, s.length ≤ (run (ps.take j)).length) →
    (run ps).length = s.length →
    ∃ m, 0 < m ∧ m ≤ ps.length ∧ (run (ps.take m)).length = s.length ∧
      ∀ j, 0 < j → j < m → s.length < (run (ps.take j)).length := by
  intro ps s w run hrun hN hpos hnn hfin
  have hsum : ∀ p : List (Bool × Bool),
      (p.map stepZ).sum = (p.countP (fun q => !q.1) : ℤ) - (p.countP (fun q => q.1 && q.2) : ℤ) := by
    intro p
    induction p with
    | nil => simp
    | cons q p ih =>
      obtain ⟨a, b⟩ := q
      cases a <;> cases b <;> simp [stepZ, ih] <;> omega
  -- the height along a prefix is the start height plus the signed sum of its steps
  have key : ∀ p : List (Bool × Bool), p.countP (fun q => q.1 && q.2) + 1 ≤ s.length →
      ((run p).length : ℤ) = (s.length : ℤ) + (p.map stepZ).sum := by
    intro p hp
    have h175 : ((p.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1.length
        + p.countP (fun q => q.1 && q.2)
        = s.length + p.countP (fun q => !q.1) :=
      MPP.Solutions.Pnp175.main p s w hp
    rw [hrun p, hsum p]
    omega
  -- every prefix satisfies the NAND hypothesis of pnp-175
  have hprefix : ∀ j, (ps.take j).countP (fun q => q.1 && q.2) + 1 ≤ s.length := by
    intro j
    have hsub : (ps.take j).countP (fun q => q.1 && q.2) ≤ ps.countP (fun q => q.1 && q.2) :=
      (List.take_sublist j ps).countP_le
    omega
  have htake : ∀ j, (ps.map stepZ).take j = (ps.take j).map stepZ := fun j => by simp
  have hsum0 : (ps.map stepZ).sum = 0 := by
    have h := key ps hN
    omega
  have hnn' : ∀ j ≤ (ps.map stepZ).length, 0 ≤ ((ps.map stepZ).take j).sum := by
    intro j hj
    rw [htake]
    have h1 := hnn j (by simpa using hj)
    have h2 := key (ps.take j) (hprefix j)
    omega
  obtain ⟨m, hm0, hmle, hmsum, hmpos⟩ :=
    zero_first_return (ps.map stepZ) (by simpa using hpos) hnn' hsum0
  rw [htake] at hmsum
  have hmpos' : ∀ j, 0 < j → j < m → 0 < ((ps.take j).map stepZ).sum := fun j hj1 hj2 => by
    have := hmpos j hj1 hj2
    rwa [htake] at this
  refine ⟨m, hm0, by simpa using hmle, ?_, fun j hj1 hj2 => ?_⟩
  · have h := key (ps.take m) (hprefix m)
    have h2 : ((run (ps.take m)).length : ℤ) = s.length := by omega
    exact_mod_cast h2
  · have h := key (ps.take j) (hprefix j)
    have := hmpos' j hj1 hj2
    omega

end MPP.Solutions.Pnp192
