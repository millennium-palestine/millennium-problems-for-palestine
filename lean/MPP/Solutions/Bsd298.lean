import Mathlib
import MPP.Solutions.Bsd282
import MPP.Solutions.Bsd283

namespace MPP.Solutions.Bsd298

open Polynomial

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/-- Exact Bezout identity for preΨ′ 5 in characteristic 3 with a₁ = a₂ = a₃ = 0. Over ℤ,
U·F + V·F′ = a₄¹² + 3·Q, so it holds in every ring with 3 = 0. -/
theorem cert {K : Type} [Field K] (h3 : (3 : K) = 0) (a4 a6 : K) (f : K[X])
    (hf : f = (2 * X ^ 6 + 5 * (2 * C a4) * X ^ 4 + 10 * (4 * C a6) * X ^ 3 + 10 * (-(C a4 ^ 2)) * X ^ 2 + (-(2 * C a4) * (4 * C a6)) * X + ((2 * C a4) * (-(C a4 ^ 2)) - (4 * C a6) ^ 2)) * (4 * X ^ 3 + 2 * (2 * C a4) * X + 4 * C a6) ^ 2 - (3 * X ^ 4 + 3 * (2 * C a4) * X ^ 2 + 3 * (4 * C a6) * X + (-(C a4 ^ 2))) ^ 3) :
    ∃ U V : K[X], U * f + V * derivative f = C (a4 ^ 12) := by
  refine ⟨(2 : K[X]) * X ^ 6 * C a4 ^ 3 + X ^ 4 * C a4 ^ 4 + X ^ 3 * C a4 ^ 3 * C a6 + (2 : K[X]) * X ^ 2 * C a4 ^ 5 + X ^ 1 * C a4 ^ 4 * C a6 + C a4 ^ 6 + (2 : K[X]) * C a4 ^ 3 * C a6 ^ 2, X ^ 9 * C a4 ^ 2 + X ^ 3 * C a4 ^ 5 + C a4 ^ 2 * C a6 ^ 3, ?_⟩
  subst hf
  have h3P : (3 : K[X]) = 0 := by rw [← map_ofNat C 3, h3, map_zero]
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_pow, derivative_C,
    derivative_X, derivative_X_pow, derivative_ofNat, map_pow, map_mul, map_sub, map_add, map_neg, map_ofNat,
    Nat.cast_ofNat, map_natCast]
  linear_combination ((20 : K[X]) * X ^ 20 * C a4 ^ 2 + (210 : K[X]) * X ^ 18 * C a4 ^ 3 + (1140 : K[X]) * X ^ 17 * C a4 ^ 2 * C a6 + (-237 : K[X]) * X ^ 16 * C a4 ^ 4 + (815 : K[X]) * X ^ 15 * C a4 ^ 3 * C a6 + (-626 : K[X]) * X ^ 14 * C a4 ^ 5 + (-480 : K[X]) * X ^ 14 * C a4 ^ 2 * C a6 ^ 2 + (-851 : K[X]) * X ^ 13 * C a4 ^ 4 * C a6 + (-152 : K[X]) * X ^ 12 * C a4 ^ 6 + (-2590 : K[X]) * X ^ 12 * C a4 ^ 3 * C a6 ^ 2 + (915 : K[X]) * X ^ 11 * C a4 ^ 5 * C a6 + (-1580 : K[X]) * X ^ 11 * C a4 ^ 2 * C a6 ^ 3 + (-546 : K[X]) * X ^ 10 * C a4 ^ 7 + (-1272 : K[X]) * X ^ 10 * C a4 ^ 4 * C a6 ^ 2 + (393 : K[X]) * X ^ 9 * C a4 ^ 6 * C a6 + (-900 : K[X]) * X ^ 9 * C a4 ^ 3 * C a6 ^ 3 + (-910 : K[X]) * X ^ 8 * C a4 ^ 8 + (-1662 : K[X]) * X ^ 8 * C a4 ^ 5 * C a6 ^ 2 + (1140 : K[X]) * X ^ 8 * C a4 ^ 2 * C a6 ^ 4 + (-1779 : K[X]) * X ^ 7 * C a4 ^ 7 * C a6 + (-1800 : K[X]) * X ^ 7 * C a4 ^ 4 * C a6 ^ 3 + (-366 : K[X]) * X ^ 6 * C a4 ^ 9 + (-4480 : K[X]) * X ^ 6 * C a4 ^ 6 * C a6 ^ 2 + (-304 : K[X]) * X ^ 6 * C a4 ^ 3 * C a6 ^ 4 + (-457 : K[X]) * X ^ 5 * C a4 ^ 8 * C a6 + (-4664 : K[X]) * X ^ 5 * C a4 ^ 5 * C a6 ^ 3 + (-480 : K[X]) * X ^ 5 * C a4 ^ 2 * C a6 ^ 5 + (-108 : K[X]) * X ^ 4 * C a4 ^ 10 + (-1114 : K[X]) * X ^ 4 * C a4 ^ 7 * C a6 ^ 2 + (-3272 : K[X]) * X ^ 4 * C a4 ^ 4 * C a6 ^ 4 + (-143 : K[X]) * X ^ 3 * C a4 ^ 9 * C a6 + (-1484 : K[X]) * X ^ 3 * C a4 ^ 6 * C a6 ^ 3 + (-3712 : K[X]) * X ^ 3 * C a4 ^ 3 * C a6 ^ 5 + (-16 : K[X]) * X ^ 2 * C a4 ^ 11 + (-168 : K[X]) * X ^ 2 * C a4 ^ 8 * C a6 ^ 2 + (-624 : K[X]) * X ^ 2 * C a4 ^ 5 * C a6 ^ 4 + (-1600 : K[X]) * X ^ 2 * C a4 ^ 2 * C a6 ^ 6 + (-33 : K[X]) * X ^ 1 * C a4 ^ 10 * C a6 + (-324 : K[X]) * X ^ 1 * C a4 ^ 7 * C a6 ^ 3 + (-672 : K[X]) * X ^ 1 * C a4 ^ 4 * C a6 ^ 5 + (-10 : K[X]) * C a4 ^ 9 * C a6 ^ 2 + (-140 : K[X]) * C a4 ^ 6 * C a6 ^ 4 + (-384 : K[X]) * C a4 ^ 3 * C a6 ^ 6) * h3P

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic],
    (3 : K) = 0 → (5 : K) ≠ 0 → W.a₁ = 0 → W.a₂ = 0 → W.a₃ = 0 → Squarefree (W.preΨ' 5) := by
  intro K _ W _ h3 _ ha1 ha2 ha3
  have hb2 : W.b₂ = 0 := by simp [WeierstrassCurve.b₂, ha1, ha2]
  have hb4 : W.b₄ = 2 * W.a₄ := by simp [WeierstrassCurve.b₄, ha1, ha3]
  have hb6 : W.b₆ = 4 * W.a₆ := by simp [WeierstrassCurve.b₆, ha3]
  have hb8 : W.b₈ = -W.a₄ ^ 2 := by simp [WeierstrassCurve.b₈, ha1, ha2, ha3]
  have hΔ : W.Δ = -(64 * W.a₄ ^ 3) - 432 * W.a₆ ^ 2 := by
    unfold WeierstrassCurve.Δ
    rw [hb2, hb4, hb6, hb8]
    ring
  have hu : IsUnit W.Δ := W.isUnit_Δ
  have ha4 : W.a₄ ≠ 0 := by
    intro h
    apply hu.ne_zero
    rw [hΔ, h]
    linear_combination (-144 * W.a₆ ^ 2) * h3
  have key : W.preΨ' 5 = (2 * X ^ 6 + 5 * (2 * C W.a₄) * X ^ 4 + 10 * (4 * C W.a₆) * X ^ 3 + 10 * (-(C W.a₄ ^ 2)) * X ^ 2 + (-(2 * C W.a₄) * (4 * C W.a₆)) * X + ((2 * C W.a₄) * (-(C W.a₄ ^ 2)) - (4 * C W.a₆) ^ 2)) * (4 * X ^ 3 + 2 * (2 * C W.a₄) * X + 4 * C W.a₆) ^ 2 - (3 * X ^ 4 + 3 * (2 * C W.a₄) * X ^ 2 + 3 * (4 * C W.a₆) * X + (-(C W.a₄ ^ 2))) ^ 3 := by
    rw [MPP.Solutions.Bsd283.main K W]
    simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, hb2, hb4, hb6,
      hb8, map_pow, map_mul, map_sub, map_add, map_neg, map_ofNat, map_zero]
    ring
  obtain ⟨U, V, hUV⟩ := cert h3 W.a₄ W.a₆ (W.preΨ' 5) key
  exact MPP.Solutions.Bsd282.main K _ U V _ (pow_ne_zero _ ha4) hUV

end MPP.Solutions.Bsd298
