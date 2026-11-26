import Mathlib

namespace MPP.Solutions.Pnp256

theorem main : ∀ s : List Bool × List Bool × Option Bool, s.2.2 = none →
    [true, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) s = s := by
  rintro ⟨st, w, p⟩ h
  simp only at h
  subst h
  rfl

end MPP.Solutions.Pnp256
