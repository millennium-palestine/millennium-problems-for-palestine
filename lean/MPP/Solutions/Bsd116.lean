import Mathlib
import MPP.Solutions.Bsd078

namespace MPP.Solutions.Bsd116

theorem key_lemma {G : Type} [CommGroup G] (a b c : G) (h1 : a * b * c = 1) (hb : b * b = 1)
    (hc : c * c = 1) : a = b * c := by
  calc a = a * (b * b) * (c * c) := by rw [hb, hc, mul_one, mul_one]
    _ = (a * b * c) * (b * c) := by ac_rfl
    _ = b * c := by rw [h1, one_mul]

theorem main : ∀ (p q e : ℚ) (g : Polynomial ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q → e ^ 3 + p * e + q = 0 →
    g = Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) → Irreducible g →
    ∃ κ : E.toAffine.Point →+ Additive ((AdjoinRoot g)ˣ ⧸ (powMonoidHom (2 : ℕ) : (AdjoinRoot g)ˣ →* (AdjoinRoot g)ˣ).range),
      ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y), ∃ u : (AdjoinRoot g)ˣ,
        (u : AdjoinRoot g) = AdjoinRoot.of g x - AdjoinRoot.root g ∧
          κ (WeierstrassCurve.Affine.Point.some x y h) = Additive.ofMul (QuotientGroup.mk u) := by
  intro p q e g E _ ha1 ha2 ha3 ha4 ha6 hcub hgdef hirr
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hal : ∀ x : ℚ, algebraMap ℚ (AdjoinRoot g) x = AdjoinRoot.of g x :=
    fun x => (eq_ratCast _ x).trans (eq_ratCast _ x).symm
  have hdeg : g.degree = 2 := by
    rw [hgdef]
    compute_degree!
  -- θ = root g satisfies the quadratic g and the cubic
  have hθq : AdjoinRoot.root g ^ 2 + AdjoinRoot.of g e * AdjoinRoot.root g +
      (AdjoinRoot.of g e ^ 2 + AdjoinRoot.of g p) = 0 := by
    have h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p)) = 0 := by
      rw [← hgdef]
      exact AdjoinRoot.mk_self
    simp only [map_add, map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h0
    exact h0
  have htθ : AdjoinRoot.root g ^ 3 + AdjoinRoot.of g p * AdjoinRoot.root g + AdjoinRoot.of g q = 0 := by
    have hq := congrArg (AdjoinRoot.of g) hcub
    simp only [map_add, map_mul, map_pow, map_zero] at hq
    linear_combination (AdjoinRoot.root g - AdjoinRoot.of g e) * hθq + hq
  -- θ is not a rational point of L
  have hθne : ∀ a : ℚ, AdjoinRoot.of g a ≠ AdjoinRoot.root g := by
    intro a ha
    have hev : g.eval a = a ^ 2 + e * a + (e ^ 2 + p) := by
      rw [hgdef]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
    have hval : AdjoinRoot.of g (g.eval a) = 0 := by
      rw [hev]
      simp only [map_add, map_mul, map_pow]
      rw [ha]
      linear_combination hθq
    have hga : g.eval a = 0 := (map_eq_zero_iff _ (AdjoinRoot.of g).injective).mp hval
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := a) hga
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  have hsub : ∀ x : ℚ, AdjoinRoot.of g x - AdjoinRoot.root g ≠ 0 := fun x => sub_ne_zero.mpr (hθne x)
  -- every class modulo squares is its own inverse, written additively
  set Rsq := (powMonoidHom (2 : ℕ) : (AdjoinRoot g)ˣ →* (AdjoinRoot g)ˣ).range with hRsq
  have hsq : ∀ u : (AdjoinRoot g)ˣ, QuotientGroup.mk u * QuotientGroup.mk u =
      (1 : (AdjoinRoot g)ˣ ⧸ Rsq) := by
    intro u
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨u, by simp [sq]⟩
  have hsqA : ∀ u : (AdjoinRoot g)ˣ,
      Additive.ofMul (QuotientGroup.mk u : (AdjoinRoot g)ˣ ⧸ Rsq) +
        Additive.ofMul (QuotientGroup.mk u : (AdjoinRoot g)ˣ ⧸ Rsq) = 0 := by
    intro u
    rw [← ofMul_mul]
    exact (congrArg Additive.ofMul (hsq u)).trans ofMul_one
  -- the product of three classes of squares is trivial
  have hclass : ∀ (a b c r : AdjoinRoot g) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0), r ≠ 0 →
      a * b * c = r ^ 2 →
      QuotientGroup.mk (Units.mk0 a ha) * QuotientGroup.mk (Units.mk0 b hb) *
        QuotientGroup.mk (Units.mk0 c hc) = (1 : (AdjoinRoot g)ˣ ⧸ Rsq) := by
    intro a b c r ha hb hc hr0 h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    simpa [powMonoidHom_apply] using h.symm
  -- the Kummer map: the class of x − θ modulo squares, and 0 at the origin
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : E.toAffine.Point → Additive ((AdjoinRoot g)ˣ ⧸ Rsq),
      κ 0 = 0 ∧ ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        κ (WeierstrassCurve.Affine.Point.some x y h) =
          Additive.ofMul (QuotientGroup.mk (Units.mk0 (AdjoinRoot.of g x - AdjoinRoot.root g) (hsub x))) := by
    refine ⟨fun P => match P with
      | WeierstrassCurve.Affine.Point.zero => 0
      | WeierstrassCurve.Affine.Point.some x _ _ =>
          Additive.ofMul (QuotientGroup.mk (Units.mk0 (AdjoinRoot.of g x - AdjoinRoot.root g) (hsub x))),
      rfl, fun x y h => rfl⟩
  -- κ is a homomorphism
  have hadd : ∀ P Q : E.toAffine.Point, κ (P + Q) = κ P + κ Q := by
    intro P Q
    rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
    · show κ 0 = κ 0 + κ 0
      rw [hκ0]
      exact (add_zero (0 : Additive ((AdjoinRoot g)ˣ ⧸ Rsq))).symm
    · show κ (WeierstrassCurve.Affine.Point.some x2 y2 h2) =
        κ 0 + κ (WeierstrassCurve.Affine.Point.some x2 y2 h2)
      rw [hκ0]
      exact (zero_add (κ (WeierstrassCurve.Affine.Point.some x2 y2 h2))).symm
    · show κ (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
        κ (WeierstrassCurve.Affine.Point.some x1 y1 h1) + κ 0
      rw [hκ0]
      exact (add_zero (κ (WeierstrassCurve.Affine.Point.some x1 y1 h1))).symm
    · by_cases hc : x1 = x2 ∧ y1 = E.toAffine.negY x2 y2
      · obtain ⟨rfl, hy⟩ := hc
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy, hκ0, hκ, hκ]
        exact (hsqA _).symm
      · have hsum := WeierstrassCurve.Affine.Point.add_some hc (h₁ := h1) (h₂ := h2)
        obtain ⟨r, hr⟩ := MPP.Solutions.Bsd078.main p q (AdjoinRoot g) (AdjoinRoot.root g) E ha1 ha2 ha3 ha4 ha6
          (by rw [hal, hal]; exact htθ)
          x1 y1 x2 y2 _ _ h1 h2 (WeierstrassCurve.Affine.nonsingular_add h1 h2 hc) hsum
          (by rw [hal]; exact hθne x1) (by rw [hal]; exact hθne x2)
        rw [hal, hal, hal] at hr
        have hr0 : r ≠ 0 := by
          rintro rfl
          rw [zero_pow two_ne_zero] at hr
          rcases mul_eq_zero.mp hr with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · exact hsub _ h'
            · exact hsub x1 h'
          · exact hsub x2 h
        rw [hsum, hκ, hκ, hκ]
        rw [← ofMul_mul]
        exact congrArg Additive.ofMul
          (key_lemma (G := (AdjoinRoot g)ˣ ⧸ Rsq) _ _ _ (hclass _ _ _ r (hsub _) (hsub x1) (hsub x2) hr0 hr)
            (hsq _) (hsq _))
  exact ⟨AddMonoidHom.mk' κ hadd, fun x y h => ⟨Units.mk0 _ (hsub x), rfl, hκ x y h⟩⟩

end MPP.Solutions.Bsd116
