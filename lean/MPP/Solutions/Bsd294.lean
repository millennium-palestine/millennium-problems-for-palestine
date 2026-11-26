import Mathlib
import MPP.Solutions.Bsd295
import MPP.Solutions.Bsd296
import MPP.Solutions.Bsd297

namespace MPP.Solutions.Bsd294

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    ((2 : K) = 0 ∨ (3 : K) = 0) → (5 : K) ≠ 0 → Squarefree (W.preΨ' 5) := by
  intro K _ _ W hW h23 h5
  rcases h23 with h2 | h3
  · exact MPP.Solutions.Bsd297.main K W h2 h5
  · have h2' : (2 : K) ≠ 0 := by
      intro h
      have h1 : (1 : K) = 0 := by linear_combination h3 - h
      exact one_ne_zero h1
    obtain ⟨W', ha1, ha3, hΔ, hψ⟩ := MPP.Solutions.Bsd295.main K W h2'
    haveI : W'.IsElliptic := ⟨by rw [hΔ]; exact hW.isUnit⟩
    have hsq := MPP.Solutions.Bsd296.main K W' h3 h5 ha1 ha3
    rw [← hψ]
    exact hsq

end MPP.Solutions.Bsd294
