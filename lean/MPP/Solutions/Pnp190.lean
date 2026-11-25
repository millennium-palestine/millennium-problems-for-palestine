import Mathlib
import MPP.Solutions.Pnp175

namespace MPP.Solutions.Pnp190

/-- The height step of a pair: -1 for a NAND pair, 0 for a no-op, +1 for a leaf or a copy. -/
def stepZ (q : Bool × Bool) : ℤ := if q.1 && q.2 then -1 else if q.1 then 0 else 1

/-- The walk lemma (pnp-189), proved here as a helper. -/
theorem walk_first_hit (d : List ℤ) (hd : ∀ e ∈ d, -1 ≤ e ∧ e ≤ 1) (hneg : d.sum < 0) :
    ∃ k, k < d.length ∧ (d.take (k + 1)).sum = -1 ∧ ∀ j ≤ k, 0 ≤ (d.take j).sum := by
  have hex : ∃ m, (d.take m).sum < 0 := ⟨d.length, by simpa using hneg⟩
  have hm : (d.take (Nat.find hex)).sum < 0 := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → 0 ≤ (d.take j).sum := fun j hj =>
    not_lt.mp (Nat.find_min hex hj)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hm
    simp at hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hkl : k < d.length := by
    have hle : Nat.find hex ≤ d.length := Nat.find_min' hex (by simpa using hneg)
    omega
  have hstep : (d.take (k + 1)).sum = (d.take k).sum + d[k] := by
    rw [List.sum_take_succ d k hkl]
  have hdk : -1 ≤ d[k] := (hd _ (List.getElem_mem hkl)).1
  have h1 : 0 ≤ (d.take k).sum := hmin k (by omega)
  rw [hk] at hm
  refine ⟨k, hkl, ?_, fun j hj => hmin j (by omega)⟩
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
    (run ps).length < s.length →
    ∃ k, k < ps.length ∧ (run (ps.take (k + 1))).length + 1 = s.length ∧
      ∀ j ≤ k, s.length ≤ (run (ps.take j)).length := by
  intro ps s w run hrun hN hfin
  -- the signed sum of the steps is the signed count of leaves and copies minus NANDs
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
    -- restated in this file: the match auxiliaries of pnp-175 are a different constant, defeq to these
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
  have hall : ∀ e ∈ ps.map stepZ, -1 ≤ e ∧ e ≤ 1 := by
    intro e he
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
    obtain ⟨a, b⟩ := q
    cases a <;> cases b <;> simp [stepZ]
  have hneg : (ps.map stepZ).sum < 0 := by
    have h := key ps hN
    omega
  obtain ⟨k, hkl, hk1, hk2⟩ := walk_first_hit (ps.map stepZ) hall hneg
  have htake : ∀ j, (ps.map stepZ).take j = (ps.take j).map stepZ := fun j => by simp
  simp only [htake] at hk1 hk2
  refine ⟨k, by simpa using hkl, ?_, fun j hj => ?_⟩
  · have h := key (ps.take (k + 1)) (hprefix (k + 1))
    omega
  · have h := key (ps.take j) (hprefix j)
    have := hk2 j hj
    omega

end MPP.Solutions.Pnp190
