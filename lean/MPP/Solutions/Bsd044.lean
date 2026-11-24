import Mathlib
import MPP.Solutions.Bsd037
import MPP.Solutions.Bsd049
import MPP.Solutions.Bsd050
import MPP.Solutions.Bsd051

namespace MPP.Solutions.Bsd044

-- the chord formula for the x-coordinate of a sum with distinct x-coordinates
theorem chord_x (E : WeierstrassCurve ℚ) (x1 y1 x2 y2 : ℚ) (h1 : E.toAffine.Nonsingular x1 y1)
    (h2 : E.toAffine.Nonsingular x2 y2) (hx : x1 ≠ x2) :
    ∃ (x3 y3 : ℚ) (h3 : E.toAffine.Nonsingular x3 y3),
      WeierstrassCurve.Affine.Point.some x1 y1 h1 + WeierstrassCurve.Affine.Point.some x2 y2 h2 = WeierstrassCurve.Affine.Point.some x3 y3 h3 ∧
      x3 = ((y1 - y2) / (x1 - x2)) ^ 2 + E.a₁ * ((y1 - y2) / (x1 - x2)) - E.a₂ - x1 - x2 := by
  refine ⟨_, _, WeierstrassCurve.Affine.nonsingular_add h1 h2 (fun hxy => hx hxy.left), WeierstrassCurve.Affine.Point.add_of_X_ne hx, ?_⟩
  unfold WeierstrassCurve.Affine.addX
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]

-- logarithmic bounds, quadratic and quartic in the heights
theorem log_quad (K A B m : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hle : m ≤ K * A ^ 2 * B ^ 2) :
    Real.log (1 + m) ≤ Real.log (K + 1) + 2 * Real.log (1 + A) + 2 * Real.log (1 + B) := by
  have hX : 1 + A ^ 2 * B ^ 2 ≤ (1 + A) ^ 2 * (1 + B) ^ 2 := by
    nlinarith [mul_nonneg hA hB, mul_nonneg (mul_nonneg hA hB) (mul_nonneg hA hB),
      mul_nonneg hA hA, mul_nonneg hB hB]
  have hY : 1 + m ≤ (K + 1) * ((1 + A) ^ 2 * (1 + B) ^ 2) := by
    have h1 : (K + 1) * (1 + A ^ 2 * B ^ 2) ≤ (K + 1) * ((1 + A) ^ 2 * (1 + B) ^ 2) :=
      mul_le_mul_of_nonneg_left hX (by linarith)
    nlinarith [mul_nonneg hK (sq_nonneg (A * B))]
  have hpos : 0 < (1 + A) ^ 2 * (1 + B) ^ 2 := by positivity
  have hlog := Real.log_le_log (by linarith) hY
  rw [Real.log_mul (by linarith) hpos.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

theorem log_quartic (K A m : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hle : m ≤ K * A ^ 4) :
    Real.log (1 + m) ≤ Real.log (K + 1) + 4 * Real.log (1 + A) := by
  have hX : 1 + A ^ 4 ≤ (1 + A) ^ 4 := by
    nlinarith [mul_nonneg hA hA, mul_nonneg (mul_nonneg hA hA) (mul_nonneg hA hA),
      mul_nonneg hA (mul_nonneg hA hA), pow_nonneg hA 3]
  have hY : 1 + m ≤ (K + 1) * (1 + A) ^ 4 := by
    have h1 : (K + 1) * (1 + A ^ 4) ≤ (K + 1) * (1 + A) ^ 4 :=
      mul_le_mul_of_nonneg_left hX (by linarith)
    nlinarith [pow_nonneg hA 4]
  have hpos : 0 < (1 + A) ^ 4 := by positivity
  have hlog := Real.log_le_log (by linarith) hY
  rw [Real.log_mul (by linarith) hpos.ne', Real.log_pow] at hlog
  push_cast at hlog
  linarith

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (H : E.toAffine.Point → ℝ),
    (∀ P : E.toAffine.Point, H P = match P with
      | WeierstrassCurve.Affine.Point.zero => 0
      | WeierstrassCurve.Affine.Point.some x _ _ =>
          Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ))) →
    ∃ C : ℝ, ∀ P Q : E.toAffine.Point, H (P + Q) ≤ 2 * H P + 2 * H Q + C := by
  intro E _ H hH
  have hH0 : H 0 = 0 := by
    rw [hH]
  have hHs : ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
      H (WeierstrassCurve.Affine.Point.some x y h) = Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ)) :=
    fun x y h => by rw [hH]
  have hnn : ∀ P : E.toAffine.Point, 0 ≤ H P := by
    intro P
    cases P with
    | zero => exact le_of_eq hH0.symm
    | some x y h =>
      rw [hHs]
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ max (x.num.natAbs : ℝ) (x.den : ℝ) := le_max_of_le_left (Nat.cast_nonneg _)
      linarith
  obtain ⟨KA, hKA⟩ := Bsd050.main E.a₁ E.a₂ E.a₃ E.a₄ E.a₆
  obtain ⟨KB, hKB⟩ := Bsd051.main E.b₂ E.b₄ E.b₆ E.b₈
  have hCA : 0 ≤ Real.log ((KA : ℝ) + 1) := Real.log_nonneg (by have : (0 : ℝ) ≤ KA := Nat.cast_nonneg _; linarith)
  have hCB : 0 ≤ Real.log ((KB : ℝ) + 1) := Real.log_nonneg (by have : (0 : ℝ) ≤ KB := Nat.cast_nonneg _; linarith)
  refine ⟨Real.log ((KA : ℝ) + 1) + Real.log ((KB : ℝ) + 1), ?_⟩
  have hC0 : 0 ≤ Real.log ((KA : ℝ) + 1) + Real.log ((KB : ℝ) + 1) := by linarith
  intro P Q
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · show H ((0 : E.toAffine.Point) + 0) ≤ 2 * H 0 + 2 * H 0 + _
    rw [add_zero, hH0]
    linarith
  · show H ((0 : E.toAffine.Point) + WeierstrassCurve.Affine.Point.some x2 y2 h2) ≤ 2 * H 0 + 2 * H (WeierstrassCurve.Affine.Point.some x2 y2 h2) + _
    rw [zero_add, hH0]
    linarith [hnn (WeierstrassCurve.Affine.Point.some x2 y2 h2)]
  · show H (WeierstrassCurve.Affine.Point.some x1 y1 h1 + (0 : E.toAffine.Point)) ≤ 2 * H (WeierstrassCurve.Affine.Point.some x1 y1 h1) + 2 * H 0 + _
    rw [add_zero, hH0]
    linarith [hnn (WeierstrassCurve.Affine.Point.some x1 y1 h1)]
  by_cases hx : x1 = x2
  · subst hx
    have hc1 := (E.toAffine.equation_iff x1 y1).mp h1.1
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with hy | hy
    · subst hy
      have hq : WeierstrassCurve.Affine.Point.some x1 y1 h2 = WeierstrassCurve.Affine.Point.some x1 y1 h1 := rfl
      rw [hq]
      by_cases hy2 : y1 = E.toAffine.negY x1 y1
      · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy2, hH0]
        linarith [hnn (WeierstrassCurve.Affine.Point.some x1 y1 h1), hC0]
      · obtain ⟨x', y', h', hP2, hx'⟩ := Bsd037.main E x1 y1 h1 hy2
        have hne : 2 * y1 + E.a₁ * x1 + E.a₃ ≠ 0 := by
          intro h0
          apply hy2
          unfold WeierstrassCurve.Affine.negY
          linarith
        have hG : 4 * x1 ^ 3 + E.b₂ * x1 ^ 2 + 2 * E.b₄ * x1 + E.b₆ ≠ 0 := by
          have key : 4 * x1 ^ 3 + E.b₂ * x1 ^ 2 + 2 * E.b₄ * x1 + E.b₆
              = (2 * y1 + E.a₁ * x1 + E.a₃) ^ 2 := by
            unfold WeierstrassCurve.b₂ WeierstrassCurve.b₄ WeierstrassCurve.b₆
            linear_combination (-4) * hc1
          rw [key]
          exact pow_ne_zero 2 hne
        have hxq : x' = (x1 ^ 4 - E.b₄ * x1 ^ 2 - 2 * E.b₆ * x1 - E.b₈)
            / (4 * x1 ^ 3 + E.b₂ * x1 ^ 2 + 2 * E.b₄ * x1 + E.b₆) := (eq_div_iff hG).mpr hx'
        have hb := hKB x1 hG
        rw [← hxq] at hb
        rw [hP2, hHs x' y' h', hHs x1 y1 h1]
        have hcast : ((max x'.num.natAbs x'.den : ℕ) : ℝ)
            ≤ ((KB * (max x1.num.natAbs x1.den) ^ 4 : ℕ) : ℝ) := by
          exact_mod_cast hb
        push_cast at hcast
        have hlq := log_quartic (KB : ℝ) (max (x1.num.natAbs : ℝ) (x1.den : ℝ))
          (max (x'.num.natAbs : ℝ) (x'.den : ℝ)) (Nat.cast_nonneg _)
          (le_max_of_le_left (Nat.cast_nonneg _)) (le_max_of_le_left (Nat.cast_nonneg _)) hcast
        linarith [hCA]
    · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy, hH0]
      linarith [hnn (WeierstrassCurve.Affine.Point.some x1 y1 h1), hnn (WeierstrassCurve.Affine.Point.some x1 y2 h2), hC0]
  · obtain ⟨x3, y3, h3, hP, hx3⟩ := chord_x E x1 y1 x2 y2 h1 h2 hx
    rw [hP, hHs x3 y3 h3, hHs x1 y1 h1, hHs x2 y2 h2]
    have hc1 := (E.toAffine.equation_iff x1 y1).mp h1.1
    have hc2 := (E.toAffine.equation_iff x2 y2).mp h2.1
    obtain ⟨hs, hp⟩ := Bsd049.main E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ x1 x2 y1 y2 x3
      (((y1 + y2 + E.a₁ * x2 + E.a₃) / (x1 - x2)) ^ 2 + E.a₁ * ((y1 + y2 + E.a₁ * x2 + E.a₃) / (x1 - x2))
        - E.a₂ - x1 - x2) hc1 hc2 hx hx3 rfl
    have hA := hKA x1 x2 _ _ x3 hx hs hp (by ring)
    have hcast : ((max x3.num.natAbs x3.den : ℕ) : ℝ)
        ≤ ((KA * (max x1.num.natAbs x1.den) ^ 2 * (max x2.num.natAbs x2.den) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hA
    push_cast at hcast
    have hlq := log_quad (KA : ℝ) (max (x1.num.natAbs : ℝ) (x1.den : ℝ))
      (max (x2.num.natAbs : ℝ) (x2.den : ℝ)) (max (x3.num.natAbs : ℝ) (x3.den : ℝ))
      (Nat.cast_nonneg _) (le_max_of_le_left (Nat.cast_nonneg _))
      (le_max_of_le_left (Nat.cast_nonneg _)) (le_max_of_le_left (Nat.cast_nonneg _)) hcast
    linarith [hCB]

end MPP.Solutions.Bsd044
