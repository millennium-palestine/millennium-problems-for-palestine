import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp148

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (p : List Bool) (s : List Bool × List Bool × Option Bool),
      ∃ k ≤ p.length, (p.foldl step s).2.1 = s.2.1.drop k := by
  intro step p
  induction p with
  | nil =>
    intro s
    exact ⟨0, by simp, by simp⟩
  | cons c p ih =>
    intro s
    have hone : ∃ j ≤ 1, (step s c).2.1 = s.2.1.drop j := by
      obtain ⟨a, b, o⟩ := s
      cases o with
      | none => exact ⟨0, by norm_num, by simp [step]⟩
      | some d =>
        cases d <;> cases c
        · exact ⟨1, by norm_num, by simp [step]⟩
        · exact ⟨0, by norm_num, by simp [step]⟩
        · exact ⟨0, by norm_num, by simp [step]⟩
        · exact ⟨0, by norm_num, by simp [step]⟩
    obtain ⟨j, hj, hs⟩ := hone
    obtain ⟨k, hk, hk'⟩ := ih (step s c)
    refine ⟨j + k, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [List.foldl_cons, hk', hs, List.drop_drop]

end MPP.Solutions.Pnp148
