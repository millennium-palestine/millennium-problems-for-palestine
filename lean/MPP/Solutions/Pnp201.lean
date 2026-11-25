import Mathlib
import MPP.Solutions.Pnp170
import MPP.Solutions.Pnp173
import MPP.Solutions.Pnp174
import MPP.Solutions.Pnp198

namespace MPP.Solutions.Pnp201

theorem main : ∀ (ps qs : List (Bool × Bool)),
    (∀ j, j ≤ ps.length → 0 ≤ ((ps.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    (ps.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    (∀ j, j ≤ qs.length → 0 ≤ ((qs.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    (qs.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    ∀ (t : List Bool) (v g : Bool),
      (∃ w : List Bool, w.length = (ps ++ qs).countP (fun q => !q.1 && !q.2) ∧ ∃ w' : List Bool,
        ((ps ++ qs).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = (g :: t, w', none)) ↔
      ∃ g1 : Bool,
        (∃ w : List Bool, w.length = ps.countP (fun q => !q.1 && !q.2) ∧ ∃ w' : List Bool,
          (ps.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
            match st.2.2 with
            | none => (st.1, st.2.1, some b)
            | some a =>
              if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
                else (st.1, st.2.1, none))
              else (if b then (st.1.headD false :: st.1, st.2.1, none)
                else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = (g1 :: t, w', none)) ∧
        (∃ w : List Bool, w.length = qs.countP (fun q => !q.1 && !q.2) ∧ ∃ w' : List Bool,
          (qs.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
            match st.2.2 with
            | none => (st.1, st.2.1, some b)
            | some a =>
              if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
                else (st.1, st.2.1, none))
              else (if b then (st.1.headD false :: st.1, st.2.1, none)
                else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (g1 :: t, w, none) = (g :: t, w', none)) := by
  intro ps qs hps0 hpss hqs0 hqss t v g
  have hcount : (ps ++ qs).countP (fun q : Bool × Bool => !q.1 && !q.2) =
      ps.countP (fun q : Bool × Bool => !q.1 && !q.2) + qs.countP (fun q : Bool × Bool => !q.1 && !q.2) := by
    simp [List.countP_append]
  constructor
  · rintro ⟨w, hw, w', hfold⟩
    rw [hcount] at hw
    erw [MPP.Solutions.Pnp173.main ps qs (v :: t) w] at hfold
    obtain ⟨g1, wA, hA⟩ := MPP.Solutions.Pnp198.main ps hps0 hpss t w v
    have hwA : wA = w.drop (ps.countP fun q : Bool × Bool => !q.1 && !q.2) := by
      have h := MPP.Solutions.Pnp174.main ps (v :: t) w
      erw [hA] at h
      exact h
    erw [hA] at hfold
    refine ⟨g1, ⟨w.take (ps.countP fun q : Bool × Bool => !q.1 && !q.2), ?_, ?_⟩, ⟨wA, ?_, w', hfold⟩⟩
    · rw [List.length_take]
      omega
    · obtain ⟨g', w'', h''⟩ := MPP.Solutions.Pnp198.main ps hps0 hpss t
        (w.take (ps.countP fun q : Bool × Bool => !q.1 && !q.2)) v
      have h170 := MPP.Solutions.Pnp170.main ps (v :: t) w
        (w.take (ps.countP fun q : Bool × Bool => !q.1 && !q.2)) (by simp)
      erw [h'', hA] at h170
      have hg : g1 = g' := by simpa using h170
      exact ⟨w'', by erw [h'', hg]⟩
    · rw [hwA, List.length_drop]
      omega
  · rintro ⟨g1, ⟨wa, hwa, wa', ha⟩, ⟨wb, hwb, wb', hb⟩⟩
    rw [hcount]
    refine ⟨wa ++ wb, by simp [hwa, hwb], wb', ?_⟩
    refine (MPP.Solutions.Pnp173.main ps qs (v :: t) (wa ++ wb)).trans ?_
    obtain ⟨g', w'', h''⟩ := MPP.Solutions.Pnp198.main ps hps0 hpss t (wa ++ wb) v
    have htk : (wa ++ wb).take (ps.countP fun q : Bool × Bool => !q.1 && !q.2) = wa := by
      rw [List.take_append_of_le_length (by omega)]
      simp [hwa]
    have h170 := MPP.Solutions.Pnp170.main ps (v :: t) (wa ++ wb) wa (by rw [htk]; simp [hwa])
    erw [h'', ha] at h170
    have hg : g' = g1 := by simpa using h170
    have h174 := MPP.Solutions.Pnp174.main ps (v :: t) (wa ++ wb)
    erw [h''] at h174
    have hw'' : w'' = wb := by
      have hd : (wa ++ wb).drop (ps.countP fun q : Bool × Bool => !q.1 && !q.2) = wb := by
        rw [← hwa]
        simp
      rw [← hd]
      exact h174
    erw [h'', hg, hw'']
    exact hb

end MPP.Solutions.Pnp201
