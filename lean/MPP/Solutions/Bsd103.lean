import Mathlib
import MPP.Solutions.Bsd075
import MPP.Solutions.Bsd078
import MPP.Solutions.Bsd082
import MPP.Solutions.Bsd083
import MPP.Solutions.Bsd086

namespace MPP.Solutions.Bsd103

theorem key_lemma {G : Type} [CommGroup G] (a b c : G) (h1 : a * b * c = 1) (hb : b * b = 1)
    (hc : c * c = 1) : a = b * c := by
  calc a = a * (b * b) * (c * c) := by rw [hb, hc, mul_one, mul_one]
    _ = (a * b * c) * (b * c) := by ac_rfl
    _ = b * c := by rw [h1, one_mul]

theorem main : ∀ (p q : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
    E.a₄ = p → E.a₆ = q →
    Irreducible (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q) →
    ∃ s : Finset E.toAffine.Point, ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro p q E _ ha1 ha2 ha3 ha4 ha6 hirr
  set f : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q with hfdef
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  set θ := AdjoinRoot.root f with hθdef
  set Rsq := (powMonoidHom (2 : ℕ) : (AdjoinRoot f)ˣ →* (AdjoinRoot f)ˣ).range with hRsq
  have hf0 : Polynomial.aeval θ f = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root f
  have htθ : θ ^ 3 + algebraMap ℚ (AdjoinRoot f) p * θ + algebraMap ℚ (AdjoinRoot f) q = 0 := by
    have h : Polynomial.aeval θ (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q) = 0 := by
      rw [← hfdef]
      exact hf0
    simpa using h
  -- an irreducible cubic has no rational root
  have hroot : ∀ x : ℚ, x ^ 3 + p * x + q ≠ 0 := by
    intro x hx
    have hdeg : f.degree = 3 := by
      rw [hfdef]
      compute_degree!
    have hfx : f.eval x = 0 := by
      rw [hfdef]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      linear_combination hx
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hfx
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  have hθne : ∀ x : ℚ, algebraMap ℚ (AdjoinRoot f) x ≠ θ := by
    intro x hx
    have h := hf0
    rw [← hx, Polynomial.aeval_algebraMap_apply] at h
    have hfx : f.eval x = 0 := (map_eq_zero_iff _ (algebraMap ℚ (AdjoinRoot f)).injective).mp h
    apply hroot x
    rw [hfdef] at hfx
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C] at hfx
    linear_combination hfx
  have hsub : ∀ x : ℚ, algebraMap ℚ (AdjoinRoot f) x - θ ≠ 0 := fun x => sub_ne_zero.mpr (hθne x)
  have hcurve : ∀ x y : ℚ, E.toAffine.Nonsingular x y → y ^ 2 = x ^ 3 + p * x + q := by
    intro x y h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq
  have hy_ne : ∀ x y : ℚ, E.toAffine.Nonsingular x y → y ≠ 0 := by
    intro x y h hy
    have h2 := hcurve x y h
    rw [hy] at h2
    exact hroot x (by linear_combination -h2)
  -- the Kummer map: the class of x − θ modulo squares, and 0 at the origin
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : E.toAffine.Point →
      Additive ((AdjoinRoot f)ˣ ⧸ Rsq),
      κ 0 = 0 ∧ ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        κ (WeierstrassCurve.Affine.Point.some x y h) =
          Additive.ofMul (QuotientGroup.mk (Units.mk0 (algebraMap ℚ (AdjoinRoot f) x - θ) (hsub x))) := by
    refine ⟨fun P => match P with
      | WeierstrassCurve.Affine.Point.zero => 0
      | WeierstrassCurve.Affine.Point.some x _ _ =>
          Additive.ofMul (QuotientGroup.mk (Units.mk0 (algebraMap ℚ (AdjoinRoot f) x - θ) (hsub x))),
      rfl, fun x y h => rfl⟩
  -- every class modulo squares is its own inverse, written additively
  have hsq : ∀ u : (AdjoinRoot f)ˣ, QuotientGroup.mk u * QuotientGroup.mk u =
      (1 : (AdjoinRoot f)ˣ ⧸ Rsq) := by
    intro u
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨u, by simp [sq]⟩
  have hsqA : ∀ u : (AdjoinRoot f)ˣ,
      Additive.ofMul (QuotientGroup.mk u : (AdjoinRoot f)ˣ ⧸ Rsq) +
        Additive.ofMul (QuotientGroup.mk u : (AdjoinRoot f)ˣ ⧸ Rsq) = 0 := by
    intro u
    rw [← ofMul_mul]
    exact (congrArg Additive.ofMul (hsq u)).trans ofMul_one
  -- the product of three classes of squares is trivial
  have hclass : ∀ (a b c r : AdjoinRoot f) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0), r ≠ 0 →
      a * b * c = r ^ 2 →
      QuotientGroup.mk (Units.mk0 a ha) * QuotientGroup.mk (Units.mk0 b hb) *
        QuotientGroup.mk (Units.mk0 c hc) = (1 : (AdjoinRoot f)ˣ ⧸ Rsq) := by
    intro a b c r ha hb hc hr0 h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    simpa [powMonoidHom_apply] using h.symm
  -- κ is a homomorphism
  have hadd : ∀ P Q : E.toAffine.Point, κ (P + Q) = κ P + κ Q := by
    intro P Q
    rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
    · show κ 0 = κ 0 + κ 0
      rw [hκ0]
      exact (add_zero (0 : Additive ((AdjoinRoot f)ˣ ⧸ Rsq))).symm
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
        obtain ⟨r, hr⟩ := MPP.Solutions.Bsd078.main p q (AdjoinRoot f) θ E ha1 ha2 ha3 ha4 ha6 htθ
          x1 y1 x2 y2 _ _ h1 h2 (WeierstrassCurve.Affine.nonsingular_add h1 h2 hc) hsum (hθne x1) (hθne x2)
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
          (key_lemma (G := (AdjoinRoot f)ˣ ⧸ Rsq) _ _ _ (hclass _ _ _ r (hsub _) (hsub x1) (hsub x2) hr0 hr)
            (hsq _) (hsq _))
  -- the image lies in a finite set
  obtain ⟨D, hD⟩ := MPP.Solutions.Bsd075.main p q f hfdef hirr
  obtain ⟨F, hF⟩ : ∃ F : AdjoinRoot f → Additive ((AdjoinRoot f)ˣ ⧸ Rsq),
      ∀ d (h : d ≠ 0), F d = Additive.ofMul (QuotientGroup.mk (Units.mk0 d h)) :=
    ⟨fun d => if h : d = 0 then 0 else Additive.ofMul (QuotientGroup.mk (Units.mk0 d h)),
      fun d h => dif_neg h⟩
  have hfin : (insert (0 : Additive ((AdjoinRoot f)ˣ ⧸ Rsq)) (F '' (D : Set (AdjoinRoot f)))).Finite :=
    (D.finite_toSet.image F).insert 0
  have hmem : ∀ P : E.toAffine.Point,
      κ P ∈ insert (0 : Additive ((AdjoinRoot f)ˣ ⧸ Rsq)) (F '' (D : Set (AdjoinRoot f))) := by
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · show κ 0 ∈ insert (0 : Additive ((AdjoinRoot f)ˣ ⧸ Rsq)) (F '' (D : Set (AdjoinRoot f)))
      rw [hκ0]
      exact Set.mem_insert _ _
    · obtain ⟨d, hd, u, hu⟩ := hD x y (hcurve x y h)
      rw [← hθdef] at hu
      have hd0 : d ≠ 0 := fun h0 => hsub x (hu.trans (by rw [h0, zero_mul]))
      have hu0 : u ≠ 0 := fun h0 => hsub x (hu.trans (by rw [h0]; simp))
      rw [hκ x y h]
      right
      refine ⟨d, hd, ?_⟩
      rw [hF d hd0]
      congr 1
      rw [QuotientGroup.eq]
      refine MonoidHom.mem_range.mpr ⟨Units.mk0 u hu0, ?_⟩
      apply Units.ext
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      rw [show algebraMap ℚ (AdjoinRoot f) x - θ = d * u ^ 2 from hu, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  -- equal images give a difference that is twice a point
  have hdouble : ∀ Q : E.toAffine.Point, κ Q + κ Q = 0 := by
    intro Q
    rcases Q with _ | ⟨x, y, h⟩
    · show κ 0 + κ 0 = 0
      rw [hκ0]
      exact add_zero (0 : Additive ((AdjoinRoot f)ˣ ⧸ Rsq))
    · rw [hκ]
      exact hsqA _
  have hker : ∀ P Q : E.toAffine.Point, κ P = κ Q → ∃ R : E.toAffine.Point, P = Q + 2 • R := by
    intro P Q hPQ
    have hneg : κ (-Q) = κ Q := by
      rcases Q with _ | ⟨x2, y2, h2⟩
      · show κ (-0) = κ 0
        rw [neg_zero]
      · rw [WeierstrassCurve.Affine.Point.neg_some, hκ, hκ]
    have hS : κ (P + -Q) = 0 := by
      rw [hadd, hneg, hPQ, hdouble]
    obtain ⟨S, hSdef⟩ : ∃ S, S = P + -Q := ⟨_, rfl⟩
    rw [← hSdef] at hS
    rcases S with _ | ⟨x, y, hS'⟩
    · have hPQ' : P = Q := add_neg_eq_zero.mp hSdef.symm
      exact ⟨0, by rw [hPQ']; simp⟩
    · rw [hκ] at hS
      have hone : QuotientGroup.mk (Units.mk0 (algebraMap ℚ (AdjoinRoot f) x - θ) (hsub x)) = 1 :=
        ofMul_eq_zero.mp hS
      obtain ⟨β, hβ⟩ := MonoidHom.mem_range.mp (QuotientGroup.eq_one_iff _ |>.mp hone)
      have hβL : (β : AdjoinRoot f) ^ 2 = algebraMap ℚ (AdjoinRoot f) x - θ := by
        have := congrArg Units.val hβ
        simpa [powMonoidHom_apply] using this
      obtain ⟨u, v, w, h1', h2', h3'⟩ := MPP.Solutions.Bsd083.main p q x f hfdef (β : AdjoinRoot f) hβL
      obtain ⟨R, hR⟩ := MPP.Solutions.Bsd082.main p q x y E ha1 ha2 ha3 ha4 ha6 hS' (hy_ne x y hS')
        ⟨u, v, w, h1', h2', h3'⟩
      refine ⟨R, ?_⟩
      rw [two_nsmul, hR, hSdef]
      abel
  let κ' : E.toAffine.Point →+ Additive ((AdjoinRoot f)ˣ ⧸ Rsq) := AddMonoidHom.mk' κ hadd
  obtain ⟨t, ht⟩ := MPP.Solutions.Bsd086.main E.toAffine.Point (Additive ((AdjoinRoot f)ˣ ⧸ Rsq)) κ' _ hfin
    (fun P => hmem P) (fun P Q h => hker P Q h)
  exact ⟨t, ht⟩

end MPP.Solutions.Bsd103
