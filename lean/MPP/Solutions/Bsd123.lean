import Mathlib
import MPP.Solutions.Bsd065
import MPP.Solutions.Bsd119
import MPP.Solutions.Bsd120

namespace MPP.Solutions.Bsd123

theorem key_lemma {G : Type} [CommGroup G] (a b c : G) (h1 : a * b * c = 1) (hb : b * b = 1)
    (hc : c * c = 1) : a = b * c := by
  calc a = a * (b * b) * (c * c) := by rw [hb, hc, mul_one, mul_one]
    _ = (a * b * c) * (b * c) := by ac_rfl
    _ = b * c := by rw [h1, one_mul]

theorem main : ∀ (p q e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e1 + e2 + e3 = 0 → p = e1 * e2 + e1 * e3 + e2 * e3 → q = -(e1 * e2 * e3) →
    e1 ≠ e2 → e1 ≠ e3 →
    ∃ κ : E.toAffine.Point →+ Additive (ℚˣ ⧸ (powMonoidHom (2 : ℕ) : ℚˣ →* ℚˣ).range),
      ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        (x ≠ e1 → ∃ u : ℚˣ, (u : ℚ) = x - e1 ∧
          κ (WeierstrassCurve.Affine.Point.some x y h) = Additive.ofMul (QuotientGroup.mk u)) ∧
        (x = e1 → ∃ u : ℚˣ, (u : ℚ) = (e1 - e2) * (e1 - e3) ∧
          κ (WeierstrassCurve.Affine.Point.some x y h) = Additive.ofMul (QuotientGroup.mk u)) := by
  intro p q e1 e2 e3 E _ ha1 ha2 ha3 ha4 ha6 hs hp hq h12 h13
  set Rsq := (powMonoidHom (2 : ℕ) : ℚˣ →* ℚˣ).range with hRsq
  have hc0 : (e1 - e2) * (e1 - e3) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)
  have hcub : e1 ^ 3 + p * e1 + q = 0 := by
    rw [hp, hq]
    linear_combination e1 ^ 2 * hs
  have hcurve : ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
      y ^ 2 = (x - e1) * (x - e2) * (x - e3) := by
    intro x y h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq + x ^ 2 * hs + x * hp + hq
  -- square classes in ℚˣ / squares
  have hsq : ∀ u : ℚˣ, QuotientGroup.mk u * QuotientGroup.mk u = (1 : ℚˣ ⧸ Rsq) := by
    intro u
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨u, by simp [sq]⟩
  have hsqA : ∀ u : ℚˣ, Additive.ofMul (QuotientGroup.mk u : ℚˣ ⧸ Rsq) +
      Additive.ofMul (QuotientGroup.mk u : ℚˣ ⧸ Rsq) = 0 := by
    intro u
    rw [← ofMul_mul]
    exact (congrArg Additive.ofMul (hsq u)).trans ofMul_one
  have hsq1 : ∀ (a w : ℚ) (ha : a ≠ 0) (hw : w ≠ 0), a = w ^ 2 →
      (QuotientGroup.mk (Units.mk0 a ha) : ℚˣ ⧸ Rsq) = 1 := by
    intro a w ha hw h
    rw [QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨Units.mk0 w hw, Units.ext (by simp [powMonoidHom_apply, h])⟩
  have hmul3 : ∀ (a b d r : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0), r ≠ 0 →
      a * b * d = r ^ 2 →
      QuotientGroup.mk (Units.mk0 a ha) * QuotientGroup.mk (Units.mk0 b hb) *
        QuotientGroup.mk (Units.mk0 d hd) = (1 : ℚˣ ⧸ Rsq) := by
    intro a b d r ha hb hd hr h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 r hr, ?_⟩
    apply Units.ext
    simpa [powMonoidHom_apply] using h.symm
  -- the value of the Kummer map: x − e1 away from T1, and the class of (e1 − e2)(e1 − e3) at T1
  obtain ⟨κ, hκ0, hκne, hκeq⟩ : ∃ κ : E.toAffine.Point → Additive (ℚˣ ⧸ Rsq),
      κ 0 = 0 ∧
      (∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y) (hx : x ≠ e1),
        κ (WeierstrassCurve.Affine.Point.some x y h) =
          Additive.ofMul (QuotientGroup.mk (Units.mk0 (x - e1) (sub_ne_zero.mpr hx)))) ∧
      (∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y) (hx : x = e1),
        κ (WeierstrassCurve.Affine.Point.some x y h) =
          Additive.ofMul (QuotientGroup.mk (Units.mk0 ((e1 - e2) * (e1 - e3)) hc0))) := by
    refine ⟨fun P => match P with
      | WeierstrassCurve.Affine.Point.zero => 0
      | WeierstrassCurve.Affine.Point.some x y h =>
          if hx : x = e1 then Additive.ofMul (QuotientGroup.mk (Units.mk0 ((e1 - e2) * (e1 - e3)) hc0))
          else Additive.ofMul (QuotientGroup.mk (Units.mk0 (x - e1) (sub_ne_zero.mpr hx))),
      rfl, ?_, ?_⟩
    · intro x y h hx
      exact dif_neg hx
    · intro x y h hx
      exact dif_pos hx
  -- two points with the same x-coordinate have classes that cancel
  have hκsq : ∀ (x y y' : ℚ) (h : E.toAffine.Nonsingular x y) (h' : E.toAffine.Nonsingular x y'),
      κ (WeierstrassCurve.Affine.Point.some x y h) +
        κ (WeierstrassCurve.Affine.Point.some x y' h') = 0 := by
    intro x y y' h h'
    by_cases hx : x = e1
    · rw [hκeq x y h hx, hκeq x y' h' hx]
      exact hsqA _
    · rw [hκne x y h hx, hκne x y' h' hx]
      exact hsqA _
  -- the 2-torsion point T1 = (e1, 0) is determined by its x-coordinate
  have hT1 : ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y) (h' : E.toAffine.Nonsingular e1 0),
      x = e1 → y = 0 →
        WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some e1 0 h' := by
    intro x y h h' hx hy
    subst hx
    subst hy
    rfl
  have hadd : ∀ P Q : E.toAffine.Point, κ (P + Q) = κ P + κ Q := by
    intro P Q
    rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
    · show κ 0 = κ 0 + κ 0
      rw [hκ0, add_zero]
    · show κ (WeierstrassCurve.Affine.Point.some _ _ _) = κ 0 + κ (WeierstrassCurve.Affine.Point.some _ _ _)
      rw [hκ0, zero_add]
    · show κ (WeierstrassCurve.Affine.Point.some _ _ _) = κ (WeierstrassCurve.Affine.Point.some _ _ _) + κ 0
      rw [hκ0, add_zero]
    by_cases hc : x1 = x2 ∧ y1 = E.toAffine.negY x2 y2
    · -- Q = −P, the sum is O
      obtain ⟨rfl, hy⟩ := hc
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy, hκ0]
      exact (hκsq _ _ _ h1 h2).symm
    obtain ⟨x3, y3, h3, hsum⟩ : ∃ (x3 y3 : ℚ) (h3 : E.toAffine.Nonsingular x3 y3),
        WeierstrassCurve.Affine.Point.some x1 y1 h1 + WeierstrassCurve.Affine.Point.some x2 y2 h2 =
          WeierstrassCurve.Affine.Point.some x3 y3 h3 :=
      ⟨_, _, _, WeierstrassCurve.Affine.Point.add_some hc (h₁ := h1) (h₂ := h2)⟩
    rw [hsum]
    by_cases hx12 : x1 = x2
    · -- same x-coordinate, not the negative: this is the doubling P + P
      subst hx12
      have hneg : E.toAffine.negY x1 y2 = -y2 := by
        simp [WeierstrassCurve.Affine.negY, ha1, ha3]
      have hy12 : y1 = y2 := by
        have hsq' : y1 ^ 2 = y2 ^ 2 := (hcurve _ _ h1).trans (hcurve _ _ h2).symm
        have hfac : (y1 - y2) * (y1 + y2) = 0 := by linear_combination hsq'
        rcases mul_eq_zero.mp hfac with h0 | h0
        · linarith
        · exact (hc ⟨rfl, by rw [hneg]; linarith⟩).elim
      subst hy12
      have hy0 : y1 ≠ 0 := fun h0 => hc ⟨rfl, by rw [hneg, h0, neg_zero]⟩
      have hB := MPP.Solutions.Bsd120.main p q e1 e2 e3 E ha1 ha2 ha3 ha4 ha6 hs hp hq x1 y1 x3 y3
        h1 h3 hsum hy0
      generalize hw : ((x1 - e1) ^ 2 - (e1 - e2) * (e1 - e3)) / (2 * y1) = w at hB
      by_cases hx3 : x3 = e1
      · -- the doubled point is T1: then (x1 − e1)² = (e1 − e2)(e1 − e3), a square
        rw [hκeq x3 y3 h3 hx3, hκsq x1 y1 y1 h1 h2]
        have hx1ne : x1 ≠ e1 := by
          intro h0
          apply hy0
          have : y1 ^ 2 = 0 := by rw [hcurve x1 y1 h1, h0]; ring
          exact (pow_eq_zero_iff two_ne_zero).mp this
        have hwz : w = 0 := by
          rw [hx3, sub_self] at hB
          exact (pow_eq_zero_iff two_ne_zero).mp hB.symm
        have hnum : (x1 - e1) ^ 2 - (e1 - e2) * (e1 - e3) = 0 := by
          have h2y : ((x1 - e1) ^ 2 - (e1 - e2) * (e1 - e3)) / (2 * y1) = 0 := hw.trans hwz
          rcases div_eq_zero_iff.mp h2y with h | h
          · exact h
          · exact absurd h (mul_ne_zero two_ne_zero hy0)
        have hc1 : (QuotientGroup.mk (Units.mk0 ((e1 - e2) * (e1 - e3)) hc0) : ℚˣ ⧸ Rsq) = 1 :=
          hsq1 _ (x1 - e1) hc0 (sub_ne_zero.mpr hx1ne) (by linear_combination -hnum)
        rw [hc1, ofMul_one]
      · -- the doubled point has x3 − e1 a square
        rw [hκne x3 y3 h3 hx3, hκsq x1 y1 y1 h1 h2]
        have hwne : w ≠ 0 := by
          intro h0
          apply sub_ne_zero.mpr hx3
          rw [hB, h0]
          ring
        rw [hsq1 (x3 - e1) w (sub_ne_zero.mpr hx3) hwne hB, ofMul_one]
    · -- different x-coordinates
      by_cases hx1 : x1 = e1
      · -- P = T1
        have hy1 : y1 = 0 := by
          have : y1 ^ 2 = 0 := by rw [hcurve x1 y1 h1, hx1]; ring
          exact (pow_eq_zero_iff two_ne_zero).mp this
        have hT : E.toAffine.Nonsingular e1 0 := by
          rw [← hx1, ← hy1]
          exact h1
        have hP1 := hT1 x1 y1 h1 hT hx1 hy1
        have hx2 : x2 ≠ e1 := fun h => hx12 (hx1.trans h.symm)
        rw [hP1, add_comm] at hsum
        have hB1 := MPP.Solutions.Bsd119.main p q e1 e2 e3 E ha1 ha2 ha3 ha4 ha6 hs hp hq x2 y2 x3 y3
          h2 hT h3 hsum hx2
        have hx3' : x3 - e1 ≠ 0 := fun h0 => hc0 (by rw [← hB1, h0, zero_mul])
        have hx3 : x3 ≠ e1 := fun h => hx3' (by rw [h, sub_self])
        rw [hκne x3 y3 h3 hx3, hκeq x1 y1 h1 hx1, hκne x2 y2 h2 hx2, ← ofMul_mul]
        exact congrArg Additive.ofMul (key_lemma _ _ _
          (hmul3 (x3 - e1) ((e1 - e2) * (e1 - e3)) (x2 - e1) ((e1 - e2) * (e1 - e3)) hx3' hc0
            (sub_ne_zero.mpr hx2) hc0
            (by linear_combination ((e1 - e2) * (e1 - e3)) * hB1))
          (hsq _) (hsq _))
      · by_cases hx2 : x2 = e1
        · -- Q = T1
          have hy2 : y2 = 0 := by
            have : y2 ^ 2 = 0 := by rw [hcurve x2 y2 h2, hx2]; ring
            exact (pow_eq_zero_iff two_ne_zero).mp this
          have hT : E.toAffine.Nonsingular e1 0 := by
            rw [← hx2, ← hy2]
            exact h2
          have hP2 := hT1 x2 y2 h2 hT hx2 hy2
          rw [hP2] at hsum
          have hB1 := MPP.Solutions.Bsd119.main p q e1 e2 e3 E ha1 ha2 ha3 ha4 ha6 hs hp hq x1 y1 x3 y3
            h1 hT h3 hsum hx1
          have hx3' : x3 - e1 ≠ 0 := fun h0 => hc0 (by rw [← hB1, h0, zero_mul])
          have hx3 : x3 ≠ e1 := fun h => hx3' (by rw [h, sub_self])
          rw [hκne x3 y3 h3 hx3, hκne x1 y1 h1 hx1, hκeq x2 y2 h2 hx2, ← ofMul_mul]
          exact congrArg Additive.ofMul (key_lemma _ _ _
            (hmul3 (x3 - e1) (x1 - e1) ((e1 - e2) * (e1 - e3)) ((e1 - e2) * (e1 - e3)) hx3'
              (sub_ne_zero.mpr hx1) hc0 hc0
              (by linear_combination ((e1 - e2) * (e1 - e3)) * hB1))
            (hsq _) (hsq _))
        · -- generic chord: bsd-065 gives the x-coordinate of the sum up to a square
          obtain ⟨x3', y3', h3', hsum', r, hr⟩ := MPP.Solutions.Bsd065.main p q e1 E ha1 ha2 ha3 ha4 ha6
            hcub x1 y1 x2 y2 h1 h2 hx12 hx1 hx2
          have hx3e : x3' = x3 := (WeierstrassCurve.Affine.Point.some.inj (hsum'.symm.trans hsum)).1
          rw [hx3e] at hr
          rcases eq_or_ne r 0 with hr0 | hr0
          · -- the sum is T1, so Q = −P + T1 and bsd-119 applied to −P gives the class of c
            have hx3 : x3 = e1 := by
              have h0 : x3 - e1 = 0 := by rw [hr, hr0]; ring
              exact sub_eq_zero.mp h0
            have hy3 : y3 = 0 := by
              have : y3 ^ 2 = 0 := by rw [hcurve x3 y3 h3, hx3]; ring
              exact (pow_eq_zero_iff two_ne_zero).mp this
            have hT : E.toAffine.Nonsingular e1 0 := by
              rw [← hx3, ← hy3]
              exact h3
            have hP3 := hT1 x3 y3 h3 hT hx3 hy3
            rw [hP3] at hsum
            have hn1 : E.toAffine.Nonsingular x1 (E.toAffine.negY x1 y1) :=
              (WeierstrassCurve.Affine.nonsingular_neg x1 y1).mpr h1
            have hneg1 : -(WeierstrassCurve.Affine.Point.some x1 y1 h1) =
                WeierstrassCurve.Affine.Point.some x1 (E.toAffine.negY x1 y1) hn1 := rfl
            have hQ : WeierstrassCurve.Affine.Point.some x1 (E.toAffine.negY x1 y1) hn1 +
                WeierstrassCurve.Affine.Point.some e1 0 hT =
                  WeierstrassCurve.Affine.Point.some x2 y2 h2 := by
              rw [← hneg1, ← hsum]
              abel
            have hB2 := MPP.Solutions.Bsd119.main p q e1 e2 e3 E ha1 ha2 ha3 ha4 ha6 hs hp hq x1
              (E.toAffine.negY x1 y1) x2 y2 hn1 hT h2 hQ hx1
            rw [hκeq x3 y3 h3 hx3, hκne x1 y1 h1 hx1, hκne x2 y2 h2 hx2, ← ofMul_mul]
            exact congrArg Additive.ofMul (key_lemma _ _ _
              (hmul3 _ (x1 - e1) (x2 - e1) _ hc0 (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hx2) hc0
                (by linear_combination ((e1 - e2) * (e1 - e3)) * hB2))
              (hsq _) (hsq _))
          · -- the sum is not T1: bsd-065 with r ≠ 0 gives the product of the two classes
            have hne3 : x3 - e1 ≠ 0 := by
              rw [hr]
              exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hx2))
                (pow_ne_zero 2 hr0)
            have hx3 : x3 ≠ e1 := fun h => hne3 (by rw [h, sub_self])
            rw [hκne x3 y3 h3 hx3, hκne x1 y1 h1 hx1, hκne x2 y2 h2 hx2, ← ofMul_mul]
            exact congrArg Additive.ofMul (key_lemma _ _ _
              (hmul3 (x3 - e1) (x1 - e1) (x2 - e1) ((x1 - e1) * (x2 - e1) * r) hne3
                (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hx2)
                (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hx2)) hr0)
                (by rw [hr]; ring))
              (hsq _) (hsq _))
  refine ⟨AddMonoidHom.mk' κ hadd, fun x y h => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact ⟨Units.mk0 (x - e1) (sub_ne_zero.mpr hx), rfl, hκne x y h hx⟩
  · exact ⟨Units.mk0 ((e1 - e2) * (e1 - e3)) hc0, rfl, hκeq x y h hx⟩

end MPP.Solutions.Bsd123
