import Mathlib
import MPP.Solutions.Bsd282
import MPP.Solutions.Bsd288
import MPP.Solutions.Bsd289

namespace MPP.Solutions.Bsd293

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    (2 : K) ≠ 0 → (3 : K) ≠ 0 → (5 : K) ≠ 0 → Squarefree (W.preΨ' 5) := by
  intro K _ _ W _ h2 h3 h5
  -- move W to a short form W' by a shift of x (bsd-289)
  obtain ⟨r, W', ha1, ha2, ha3, hΔ, hpre⟩ := MPP.Solutions.Bsd289.main K W h2 h3
  -- short-form Bezout certificate (bsd-288)
  obtain ⟨A, B, hAB⟩ := MPP.Solutions.Bsd288.main K W' ha1 ha2 ha3
  have hc : (5 : K) ^ 12 * W'.Δ ^ 22 ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ h5)
    apply pow_ne_zero
    rw [hΔ]
    exact W.isUnit_Δ.ne_zero
  -- transport the identity along x ↦ x − r
  apply MPP.Solutions.Bsd282.main K (W.preΨ' 5) (A.comp (Polynomial.X - Polynomial.C r))
    (B.comp (Polynomial.X - Polynomial.C r)) ((5 : K) ^ 12 * W'.Δ ^ 22) hc
  rw [hpre, Polynomial.derivative_comp, Polynomial.derivative_X_sub_C, one_mul]
  have key := congrArg (fun p => Polynomial.comp p (Polynomial.X - Polynomial.C r)) hAB
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp] at key
  exact key

end MPP.Solutions.Bsd293
