import Mathlib

namespace MPP.Solutions.Bsd289

/-- The 5-division polynomial in the form of bsd-283. -/
lemma preΨ'_five_eq {K : Type} [Field K] (W : WeierstrassCurve K) :
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 from rfl, WeierstrassCurve.preΨ'_odd]
  simp [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, pow_three]

/-- The constant term of the shifted curve, from the relation `4 b₈ = b₂ b₆ - b₄²`. -/
lemma b₈_of_shift {K : Type} [Field K] (W : WeierstrassCurve K) (r a4 a6 : K) (h4 : (4 : K) ≠ 0)
    (hb2 : W.b₂ = -12 * r) (hb4 : W.b₄ = 2 * a4 + 6 * r ^ 2)
    (hb6 : W.b₆ = 4 * a6 - 4 * r ^ 3 - 4 * r * a4) :
    W.b₈ = 3 * r ^ 4 + 6 * a4 * r ^ 2 - 12 * a6 * r - a4 ^ 2 := by
  apply mul_left_cancel₀ h4
  have h := W.b_relation
  rw [hb2, hb4, hb6] at h
  linear_combination h

/-- Shift identity for `Ψ₂Sq`. -/
lemma Ψ₂Sq_shift {K : Type} [Field K] (W V : WeierstrassCurve K) (r a4 a6 : K)
    (hb2 : W.b₂ = -12 * r) (hb4 : W.b₄ = 2 * a4 + 6 * r ^ 2)
    (hb6 : W.b₆ = 4 * a6 - 4 * r ^ 3 - 4 * r * a4)
    (hV2 : V.b₂ = 0) (hV4 : V.b₄ = 2 * a4) (hV6 : V.b₆ = 4 * a6) :
    W.Ψ₂Sq = V.Ψ₂Sq.comp (Polynomial.X - Polynomial.C r) := by
  rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₂Sq, hb2, hb4, hb6, hV2, hV4, hV6]
  simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.neg_comp, Polynomial.zero_comp, Polynomial.X_comp,
    Polynomial.C_comp, Polynomial.ofNat_comp, Polynomial.natCast_comp, Nat.cast_ofNat,
    map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, zero_mul, zero_add,
    add_zero, mul_zero, zero_sub, neg_mul, mul_neg]
  ring

/-- Shift identity for `Ψ₃`. -/
lemma Ψ₃_shift {K : Type} [Field K] (W V : WeierstrassCurve K) (r a4 a6 : K) (h4 : (4 : K) ≠ 0)
    (hb2 : W.b₂ = -12 * r) (hb4 : W.b₄ = 2 * a4 + 6 * r ^ 2)
    (hb6 : W.b₆ = 4 * a6 - 4 * r ^ 3 - 4 * r * a4)
    (hV2 : V.b₂ = 0) (hV4 : V.b₄ = 2 * a4) (hV6 : V.b₆ = 4 * a6) (hV8 : V.b₈ = -a4 ^ 2) :
    W.Ψ₃ = V.Ψ₃.comp (Polynomial.X - Polynomial.C r) := by
  rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₃, hb2, hb4, hb6,
    b₈_of_shift W r a4 a6 h4 hb2 hb4 hb6, hV2, hV4, hV6, hV8]
  simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.neg_comp, Polynomial.zero_comp, Polynomial.X_comp,
    Polynomial.C_comp, Polynomial.ofNat_comp, Polynomial.natCast_comp, Nat.cast_ofNat,
    map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, zero_mul, zero_add,
    add_zero, mul_zero, zero_sub, neg_mul, mul_neg]
  ring

/-- Shift identity for `preΨ₄`. -/
lemma preΨ₄_shift {K : Type} [Field K] (W V : WeierstrassCurve K) (r a4 a6 : K) (h4 : (4 : K) ≠ 0)
    (hb2 : W.b₂ = -12 * r) (hb4 : W.b₄ = 2 * a4 + 6 * r ^ 2)
    (hb6 : W.b₆ = 4 * a6 - 4 * r ^ 3 - 4 * r * a4)
    (hV2 : V.b₂ = 0) (hV4 : V.b₄ = 2 * a4) (hV6 : V.b₆ = 4 * a6) (hV8 : V.b₈ = -a4 ^ 2) :
    W.preΨ₄ = V.preΨ₄.comp (Polynomial.X - Polynomial.C r) := by
  rw [WeierstrassCurve.preΨ₄, WeierstrassCurve.preΨ₄, hb2, hb4, hb6,
    b₈_of_shift W r a4 a6 h4 hb2 hb4 hb6, hV2, hV4, hV6, hV8]
  simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.neg_comp, Polynomial.zero_comp, Polynomial.X_comp,
    Polynomial.C_comp, Polynomial.ofNat_comp, Polynomial.natCast_comp, Nat.cast_ofNat,
    map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero, zero_mul, zero_add,
    add_zero, mul_zero, zero_sub, neg_mul, mul_neg]
  ring

/-- The 5-division polynomial of `W` is a shift of that of the short curve `a₄, a₆`. -/
lemma preΨ'_five_shift {K : Type} [Field K] (W : WeierstrassCurve K) (r a4 a6 : K)
    (h4 : (4 : K) ≠ 0)
    (hb2 : W.b₂ = -12 * r) (hb4 : W.b₄ = 2 * a4 + 6 * r ^ 2)
    (hb6 : W.b₆ = 4 * a6 - 4 * r ^ 3 - 4 * r * a4) :
    W.preΨ' 5 = ((WeierstrassCurve.mk 0 0 0 a4 a6).preΨ' 5).comp
      (Polynomial.X - Polynomial.C r) := by
  have hV2 : (WeierstrassCurve.mk 0 0 0 a4 a6).b₂ = 0 := by
    simp only [WeierstrassCurve.b₂]; ring
  have hV4 : (WeierstrassCurve.mk 0 0 0 a4 a6).b₄ = 2 * a4 := by
    simp only [WeierstrassCurve.b₄]; ring
  have hV6 : (WeierstrassCurve.mk 0 0 0 a4 a6).b₆ = 4 * a6 := by
    simp only [WeierstrassCurve.b₆]; ring
  have hV8 : (WeierstrassCurve.mk 0 0 0 a4 a6).b₈ = -a4 ^ 2 := by
    simp only [WeierstrassCurve.b₈]; ring
  rw [preΨ'_five_eq W, preΨ'_five_eq (WeierstrassCurve.mk 0 0 0 a4 a6)]
  have e2 := Ψ₂Sq_shift W (WeierstrassCurve.mk 0 0 0 a4 a6) r a4 a6 hb2 hb4 hb6 hV2 hV4 hV6
  have e3 := Ψ₃_shift W (WeierstrassCurve.mk 0 0 0 a4 a6) r a4 a6 h4 hb2 hb4 hb6 hV2 hV4 hV6 hV8
  have e4 := preΨ₄_shift W (WeierstrassCurve.mk 0 0 0 a4 a6) r a4 a6 h4 hb2 hb4 hb6 hV2 hV4 hV6
    hV8
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp]
  rw [e2, e3, e4]

/-- Short form by a variable change, with the 5-division polynomial shifted by `r`. -/
theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    ∃ (r : K) (W' : WeierstrassCurve K), W'.a₁ = 0 ∧ W'.a₂ = 0 ∧ W'.a₃ = 0 ∧ W'.Δ = W.Δ ∧
      W.preΨ' 5 = (W'.preΨ' 5).comp (Polynomial.X - Polynomial.C r) := by
  intro K _ W h2 h3
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h12 : (12 : K) ≠ 0 := by
    have : (12 : K) = 4 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h4 h3
  obtain ⟨r, hb2⟩ : ∃ r : K, W.b₂ = -12 * r := ⟨-W.b₂ / 12, by field_simp⟩
  obtain ⟨a4, ha4⟩ : ∃ a4 : K, 2 * a4 = W.b₄ + r * W.b₂ + 6 * r ^ 2 :=
    ⟨(W.b₄ + r * W.b₂ + 6 * r ^ 2) / 2, by field_simp⟩
  obtain ⟨a6, ha6⟩ : ∃ a6 : K, 4 * a6 = W.b₆ + 2 * r * W.b₄ + r ^ 2 * W.b₂ + 4 * r ^ 3 :=
    ⟨(W.b₆ + 2 * r * W.b₄ + r ^ 2 * W.b₂ + 4 * r ^ 3) / 4, by field_simp⟩
  have hb4 : W.b₄ = 2 * a4 + 6 * r ^ 2 := by linear_combination -ha4 - r * hb2
  have hb6 : W.b₆ = 4 * a6 - 4 * r ^ 3 - 4 * r * a4 := by
    linear_combination -ha6 - 2 * r * hb4 - r ^ 2 * hb2
  refine ⟨r, WeierstrassCurve.mk 0 0 0 a4 a6, rfl, rfl, rfl, ?_,
    preΨ'_five_shift W r a4 a6 h4 hb2 hb4 hb6⟩
  rw [WeierstrassCurve.Δ, WeierstrassCurve.Δ, hb2, hb4, hb6,
    b₈_of_shift W r a4 a6 h4 hb2 hb4 hb6]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end MPP.Solutions.Bsd289
