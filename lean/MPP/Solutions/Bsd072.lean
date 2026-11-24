import Mathlib

namespace MPP.Solutions.Bsd072

open WeierstrassCurve WeierstrassCurve.Affine

/-- The x-coordinate of the image under the change of variables `C`. -/
noncomputable def tX (C : VariableChange ℚ) (x : ℚ) : ℚ := (x - C.r) / (C.u : ℚ) ^ 2

/-- The y-coordinate of the image under the change of variables `C`. -/
noncomputable def tY (C : VariableChange ℚ) (x y : ℚ) : ℚ := (y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3

/-- The inverse x-coordinate: `x = u² x′ + r`. -/
noncomputable def untX (C : VariableChange ℚ) (x : ℚ) : ℚ := (C.u : ℚ) ^ 2 * x + C.r

/-- The inverse y-coordinate: `y = u³ y′ + s u² x′ + t`. -/
noncomputable def untY (C : VariableChange ℚ) (x y : ℚ) : ℚ :=
  (C.u : ℚ) ^ 3 * y + C.s * ((C.u : ℚ) ^ 2 * x) + C.t

lemma u_ne (C : VariableChange ℚ) : (C.u : ℚ) ≠ 0 := C.u.ne_zero

lemma tX_untX (C : VariableChange ℚ) (x : ℚ) : tX C (untX C x) = x := by
  have := u_ne C
  unfold tX untX
  field_simp
  ring

lemma tY_untY (C : VariableChange ℚ) (x y : ℚ) : tY C (untX C x) (untY C x y) = y := by
  have := u_ne C
  unfold tY untX untY
  field_simp
  ring

lemma tX_inj (C : VariableChange ℚ) {a b : ℚ} (h : tX C a = tX C b) : a = b := by
  have := u_ne C
  unfold tX at h
  rw [div_left_inj' (pow_ne_zero 2 this), sub_left_inj] at h
  exact h

lemma tY_inj (C : VariableChange ℚ) (x : ℚ) {a b : ℚ} (h : tY C x a = tY C x b) : a = b := by
  have := u_ne C
  unfold tY at h
  rw [div_left_inj' (pow_ne_zero 3 this), sub_left_inj, sub_left_inj] at h
  exact h

/-- The negation formula is transported. -/
lemma negY_transport (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    (C • E).toAffine.negY (tX C x) (tY C x y) = tY C x (E.toAffine.negY x y) := by
  have := u_ne C
  unfold negY tX tY
  simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- Polynomial identity: the equation of `C • E` at the image point is the equation of `E`,
scaled by `u⁻⁶`. -/
lemma eq_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    (tY C x y) ^ 2 + (C • E).a₁ * tX C x * tY C x y + (C • E).a₃ * tY C x y
      - ((tX C x) ^ 3 + (C • E).a₂ * (tX C x) ^ 2 + (C • E).a₄ * tX C x + (C • E).a₆)
    = (((C.u : ℚ) ^ 6)⁻¹) * (y ^ 2 + E.a₁ * x * y + E.a₃ * y - (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)) := by
  have := u_ne C
  unfold tX tY
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma equation_transport (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    (C • E).toAffine.Equation (tX C x) (tY C x y) ↔ E.toAffine.Equation x y := by
  have key := eq_identity E C x y
  have hpow : ((C.u : ℚ) ^ 6)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 6 (u_ne C))
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff]
  change (tY C x y) ^ 2 + (C • E).a₁ * tX C x * tY C x y + (C • E).a₃ * tY C x y =
      (tX C x) ^ 3 + (C • E).a₂ * (tX C x) ^ 2 + (C • E).a₄ * tX C x + (C • E).a₆ ↔
    y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆
  constructor
  · intro h
    have h2 : ((C.u : ℚ) ^ 6)⁻¹ * (y ^ 2 + E.a₁ * x * y + E.a₃ * y - (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)) = 0 := by
      linear_combination (-1 : ℚ) * key + h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hpow
    · linear_combination h3
  · intro h
    linear_combination key + ((C.u : ℚ) ^ 6)⁻¹ * h

/-- The `y`-derivative identity: `2y′ + a₁′x′ + a₃′ = u⁻³ (2y + a₁x + a₃)`. -/
lemma G2_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    2 * tY C x y + (C • E).a₁ * tX C x + (C • E).a₃
      = ((C.u : ℚ) ^ 3)⁻¹ * (2 * y + E.a₁ * x + E.a₃) := by
  have := u_ne C
  unfold tX tY
  simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The `x`-derivative identity. -/
lemma G1_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    (C • E).a₁ * tY C x y - (3 * (tX C x) ^ 2 + 2 * (C • E).a₂ * tX C x + (C • E).a₄)
      = ((C.u : ℚ) ^ 4)⁻¹ * ((E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄)) +
          C.s * (2 * y + E.a₁ * x + E.a₃)) := by
  have := u_ne C
  unfold tX tY
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma aux_iff (u s G1 G2 : ℚ) (hu : u ≠ 0) :
    ((u ^ 4)⁻¹ * (G1 + s * G2) ≠ 0 ∨ (u ^ 3)⁻¹ * G2 ≠ 0) ↔ (G1 ≠ 0 ∨ G2 ≠ 0) := by
  have h4 : (u ^ 4)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 4 hu)
  have h3 : (u ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 3 hu)
  constructor
  · intro h
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    obtain ⟨g1, g2⟩ := hc
    rw [g1, g2] at h
    simp at h
  · intro h
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    obtain ⟨hA, hB⟩ := hc
    have g2 : G2 = 0 := (mul_eq_zero.mp hB).resolve_left h3
    have g1 : G1 = 0 := by
      have := (mul_eq_zero.mp hA).resolve_left h4
      rw [g2, mul_zero, add_zero] at this
      exact this
    rcases h with h | h
    · exact h g1
    · exact h g2

lemma nonsing_transport (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    (C • E).toAffine.Nonsingular (tX C x) (tY C x y) ↔ E.toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.nonsingular_iff',
    equation_transport]
  refine and_congr_right fun _ => ?_
  rw [G1_identity, G2_identity]
  exact aux_iff _ _ _ _ (u_ne C)

lemma untX_tX (C : VariableChange ℚ) (x : ℚ) : untX C (tX C x) = x := by
  have := u_ne C
  unfold tX untX
  field_simp
  ring

lemma untY_tY (C : VariableChange ℚ) (x y : ℚ) : untY C (tX C x) (tY C x y) = y := by
  have := u_ne C
  unfold tX tY untY
  field_simp
  ring

lemma nonsing_untransport (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ)
    (h : (C • E).toAffine.Nonsingular x y) :
    E.toAffine.Nonsingular (untX C x) (untY C x y) := by
  rw [← nonsing_transport, tX_untX, tY_untY]
  exact h

/-- The map on points, the coordinate change. -/
noncomputable def Fpt (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) :
    E.toAffine.Point → (C • E).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (tX C x) (tY C x y) ((nonsing_transport E C x y).mpr h)

/-- The inverse map on points. -/
noncomputable def Gpt (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) :
    (C • E).toAffine.Point → E.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (untX C x) (untY C x y) (nonsing_untransport E C x y h)

lemma some_congr {W : WeierstrassCurve ℚ} {x y x' y' : ℚ} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx hy
  rfl

lemma Fpt_zero (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) : Fpt E C 0 = 0 := rfl

lemma Fpt_some (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ)
    (h : E.toAffine.Nonsingular x y) :
    Fpt E C (Point.some x y h) = Point.some (tX C x) (tY C x y) ((nonsing_transport E C x y).mpr h) :=
  rfl

lemma Gpt_Fpt (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (P : E.toAffine.Point) :
    Gpt E C (Fpt E C P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [Fpt, Gpt]
    exact some_congr _ _ (untX_tX C x) (untY_tY C x y)

lemma Fpt_Gpt (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (Q : (C • E).toAffine.Point) :
    Fpt E C (Gpt E C Q) = Q := by
  cases Q with
  | zero => rfl
  | some x y h =>
    simp only [Fpt, Gpt]
    exact some_congr _ _ (tX_untX C x) (tY_untY C x y)

lemma tX_ne (C : VariableChange ℚ) {a b : ℚ} (h : a ≠ b) : tX C a ≠ tX C b :=
  fun h' => h (tX_inj C h')

/-- `y′` at the negation: the transported negation is the transport of the negation. -/
lemma denom_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    tY C x y - (C • E).toAffine.negY (tX C x) (tY C x y)
      = ((C.u : ℚ) ^ 3)⁻¹ * (y - E.toAffine.negY x y) := by
  rw [negY_transport]
  unfold tY
  ring

lemma numer_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x y : ℚ) :
    3 * (tX C x) ^ 2 + 2 * (C • E).a₂ * tX C x + (C • E).a₄ - (C • E).a₁ * tY C x y
      = -(((C.u : ℚ) ^ 4)⁻¹ * ((E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄)) +
          C.s * (2 * y + E.a₁ * x + E.a₃))) := by
  linear_combination (-1 : ℚ) * G1_identity E C x y

/-- The slope of the transported chord or tangent is the transported slope. -/
lemma slope_transport (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) {x1 y1 x2 y2 : ℚ}
    (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = E.toAffine.negY x2 y2)) :
    (C • E).toAffine.slope (tX C x1) (tX C x2) (tY C x1 y1) (tY C x2 y2)
      = (E.toAffine.slope x1 x2 y1 y2 - C.s) / (C.u : ℚ) := by
  have hu := u_ne C
  by_cases hx : x1 = x2
  · subst hx
    have hy12 : y1 = y2 ∨ y1 = E.toAffine.negY x1 y2 :=
      WeierstrassCurve.Affine.Y_eq_of_X_eq h1.1 h2.1 rfl
    have hy : y1 ≠ E.toAffine.negY x1 y2 := fun h => hxy ⟨rfl, h⟩
    have hy2 : y1 = y2 := hy12.resolve_right hy
    subst hy2
    have hy' : tY C x1 y1 ≠ (C • E).toAffine.negY (tX C x1) (tY C x1 y1) := by
      rw [negY_transport]
      exact fun h => hy (tY_inj C x1 h)
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, denom_identity, numer_identity]
    have hD : y1 - E.toAffine.negY x1 y1 ≠ 0 := sub_ne_zero.mpr hy
    field_simp
    unfold WeierstrassCurve.Affine.negY
    ring
  · have hx' : tX C x1 ≠ tX C x2 := tX_ne C hx
    have hX : tX C x1 - tX C x2 = (x1 - x2) / (C.u : ℚ) ^ 2 := by
      unfold tX; ring
    have hY : tY C x1 y1 - tY C x2 y2 = (y1 - y2 - C.s * (x1 - x2)) / (C.u : ℚ) ^ 3 := by
      unfold tY; ring
    have hx0 : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
    rw [slope_of_X_ne hx', slope_of_X_ne hx, hX, hY]
    field_simp

/-- The `x`-coordinate of a sum is transported. -/
lemma addX_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x1 x2 l : ℚ) :
    WeierstrassCurve.Affine.addX (C • E).toAffine (tX C x1) (tX C x2) ((l - C.s) / (C.u : ℚ))
      = tX C (WeierstrassCurve.Affine.addX E.toAffine x1 x2 l) := by
  have hu := u_ne C
  unfold WeierstrassCurve.Affine.addX tX
  simp only [variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The `y`-coordinate of a sum is transported. -/
lemma addY_identity (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (x1 y1 x2 l : ℚ) :
    WeierstrassCurve.Affine.addY (C • E).toAffine (tX C x1) (tX C x2) (tY C x1 y1)
        ((l - C.s) / (C.u : ℚ))
      = tY C (WeierstrassCurve.Affine.addX E.toAffine x1 x2 l)
          (WeierstrassCurve.Affine.addY E.toAffine x1 x2 y1 l) := by
  have hu := u_ne C
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
    WeierstrassCurve.Affine.negY tX tY
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma Fpt_add (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) (P Q : E.toAffine.Point) :
    Fpt E C (P + Q) = Fpt E C P + Fpt E C Q := by
  cases P with
  | zero =>
    change Fpt E C (0 + Q) = Fpt E C 0 + Fpt E C Q
    rw [zero_add, Fpt_zero, zero_add]
  | some x1 y1 h1 =>
    cases Q with
    | zero =>
      change Fpt E C (_ + 0) = _ + Fpt E C 0
      rw [add_zero, Fpt_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hxy : x1 = x2 ∧ y1 = E.toAffine.negY x2 y2
      · have hxy' : tX C x1 = tX C x2 ∧
            tY C x1 y1 = (C • E).toAffine.negY (tX C x2) (tY C x2 y2) := by
          refine ⟨by rw [hxy.1], ?_⟩
          rw [negY_transport, hxy.1, hxy.2]
        rw [Point.add_of_Y_eq hxy.1 hxy.2, Fpt_zero, Fpt_some, Fpt_some,
          Point.add_of_Y_eq hxy'.1 hxy'.2]
      · have hxy' : ¬(tX C x1 = tX C x2 ∧
            tY C x1 y1 = (C • E).toAffine.negY (tX C x2) (tY C x2 y2)) := by
          rintro ⟨h1', h2'⟩
          have hx : x1 = x2 := tX_inj C h1'
          rw [negY_transport, hx] at h2'
          exact hxy ⟨hx, tY_inj C x2 h2'⟩
        rw [Point.add_some hxy, Fpt_some, Fpt_some, Fpt_some, Point.add_some hxy']
        refine some_congr _ _ ?_ ?_
        · rw [slope_transport E C h1 h2 hxy]
          exact (addX_identity E C x1 x2 (E.toAffine.slope x1 x2 y1 y2)).symm
        · rw [slope_transport E C h1 h2 hxy]
          exact (addY_identity E C x1 y1 x2 (E.toAffine.slope x1 x2 y1 y2)).symm

theorem main : ∀ (E : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ),
    ∃ f : E.toAffine.Point → (C • E).toAffine.Point, Function.Bijective f ∧ ∀ P Q, f (P + Q) = f P + f Q := by
  intro E C
  exact ⟨Fpt E C, Function.bijective_iff_has_inverse.mpr ⟨Gpt E C, Gpt_Fpt E C, Fpt_Gpt E C⟩,
    fun P Q => Fpt_add E C P Q⟩

end MPP.Solutions.Bsd072
