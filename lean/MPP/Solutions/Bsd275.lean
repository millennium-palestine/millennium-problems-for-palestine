import Mathlib
import MPP.Solutions.Bsd217
import MPP.Solutions.Bsd268
import MPP.Solutions.Bsd271

namespace MPP.Solutions.Bsd275

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ ≠ 0 →
    (W.preΨ' 5).eval x = 0 →
    (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
  intro K _ _ W x y h hD hΨ hψ
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h with hPdef
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  have hy' : y ≠ -y - W.a₁ * x - W.a₃ := fun h' => hD (by linear_combination h')
  have hy : y ≠ W.toAffine.negY x y := fun h' => hy' (by simpa [WeierstrassCurve.Affine.negY] using h')
  -- the double 2P = (x₂, y₂)
  have hdbl := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hy
  obtain ⟨x₂, y₂, h₂, hP2⟩ : ∃ (x₂ y₂ : K) (h₂ : W.toAffine.Nonsingular x₂ y₂),
      P + P = WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :=
    ⟨_, _, _, hdbl⟩
  -- bsd-268: (x − x₂) g = Ψ₃(x)
  have hx2 := MPP.Solutions.Bsd268.main K W x y x₂ y₂ h h₂ hP2
  -- g = (2y + a₁x + a₃)² on the curve, so g ≠ 0
  have hg : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 := by
    intro h0
    apply hD
    have hsq : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 0 := by
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h0
      linear_combination 4 * hE + h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  -- 3P is not zero: otherwise 2P = −P and x₂ = x, which forces Ψ₃(x) = 0
  have h3ne : P + (P + P) ≠ 0 := by
    intro h0
    have hneg : P + P = -P := by
      rw [← add_eq_zero_iff_eq_neg]
      rw [add_comm] at h0
      exact h0
    rw [hP2, hPdef, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hneg
    obtain ⟨hx₂, -⟩ := hneg
    apply hΨ
    have := hx2
    rw [hx₂, sub_self, zero_mul] at this
    exact this.symm
  -- so 3P = (t, y₃) is affine, and bsd-271 gives t Ψ₃² = x Ψ₃² − preΨ₄ g
  obtain ⟨t, y₃, h₃, hT⟩ : ∃ (t y₃ : K) (h₃ : W.toAffine.Nonsingular t y₃),
      P + (P + P) = WeierstrassCurve.Affine.Point.some t y₃ h₃ := by
    cases hQ : P + (P + P) with
    | zero => exact absurd hQ h3ne
    | some t y₃ h₃ => exact ⟨t, y₃, h₃, rfl⟩
  have ht := MPP.Solutions.Bsd271.main K W x y t y₃ h h₃ hy hT
  -- ψ₅ = preΨ₄ g² − Ψ₃³ (Mathlib preΨ'_odd at m = 0)
  have hpsi5 : (W.preΨ' 5).eval x =
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 -
        (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3 := by
    have hodd := W.preΨ'_odd 0
    norm_num at hodd
    rw [hodd]
    simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃]
  -- ψ₅(x) = 0 gives Ψ₃³ = preΨ₄ g², and then x(3P) = x(2P)
  have hcop : (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3 =
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 := by
    rw [hpsi5] at hψ
    linear_combination -hψ
  have hkey : (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 2 *
      (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * (t - x₂) = 0 := by
    linear_combination (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * ht +
      (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 2 * hx2 + hcop
  have htx : t = x₂ := by
    rcases mul_eq_zero.mp hkey with h0 | h0
    · exact absurd h0 (mul_ne_zero (pow_ne_zero 2 hΨ) hg)
    · exact sub_eq_zero.mp h0
  subst htx
  -- bsd-217: 3P = ±2P, and 3P = 2P would force P = 0
  rcases MPP.Solutions.Bsd217.main K W t y₃ y₂ h₃ h₂ with hA | hB
  · exfalso
    have hEq : P + (P + P) = P + P := by rw [hT, hP2]; exact hA
    have hP0 : P = 0 := by simpa using hEq
    exact WeierstrassCurve.Affine.Point.some_ne_zero (h := h) (hPdef.symm.trans hP0)
  · have h5 : (5 : ℤ) • P = (P + (P + P)) + (P + P) := by
      rw [show (5 : ℤ) = 1 + 2 + 2 by norm_num, add_zsmul, add_zsmul, one_zsmul, two_zsmul]
    rw [h5, hT, hP2, hB, neg_add_cancel]

end MPP.Solutions.Bsd275
