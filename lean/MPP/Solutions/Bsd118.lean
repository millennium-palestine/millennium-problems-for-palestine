import Mathlib
import MPP.Solutions.Bsd113
import MPP.Solutions.Bsd115
import MPP.Solutions.Bsd116
import MPP.Solutions.Bsd117

namespace MPP.Solutions.Bsd118

theorem main : ∀ (p q e : ℚ) (g : Polynomial ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q → e ^ 3 + p * e + q = 0 →
    g = Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) → Irreducible g →
    ∃ s : Finset E.toAffine.Point, ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro p q e g E _ ha1 ha2 ha3 ha4 ha6 hcub hgdef hirr
  set Rsq := (powMonoidHom (2 : ℕ) : (AdjoinRoot g)ˣ →* (AdjoinRoot g)ˣ).range with hRsq
  obtain ⟨κ, hκ⟩ := MPP.Solutions.Bsd116.main p q e g E ha1 ha2 ha3 ha4 ha6 hcub hgdef hirr
  obtain ⟨D, hD⟩ := MPP.Solutions.Bsd115.main p e g hgdef hirr
  have hD' : ∀ x y : ℚ, y ^ 2 = (x - e) * (x ^ 2 + e * x + (e ^ 2 + p)) →
      ∃ d ∈ D, ∃ w : AdjoinRoot g, AdjoinRoot.of g x - AdjoinRoot.root g = d * w ^ 2 := by
    intro x y hxy
    obtain ⟨d, hd, w, hw⟩ := hD x y hxy
    exact ⟨d, hd, w, by rw [AdjoinRoot.algebraMap_eq] at hw; exact hw⟩
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hdeg : g.degree = 2 := by
    rw [hgdef]
    compute_degree!
  have hgne : ∀ x : ℚ, x ^ 2 + e * x + (e ^ 2 + p) ≠ 0 := by
    intro x hx
    have hev : g.eval x = 0 := by
      rw [hgdef]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
      linear_combination hx
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := x) hev
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  have hcurve : ∀ x y : ℚ, E.toAffine.Nonsingular x y → y ^ 2 = (x - e) * (x ^ 2 + e * x + (e ^ 2 + p)) := by
    intro x y h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq + hcub
  -- classes of units modulo squares, and the representative of a nonzero element
  let F : AdjoinRoot g → Additive ((AdjoinRoot g)ˣ ⧸ Rsq) := fun d =>
    if h : d = 0 then 0 else Additive.ofMul (QuotientGroup.mk (Units.mk0 d h))
  have hF : ∀ (d : AdjoinRoot g) (h : d ≠ 0), F d = Additive.ofMul (QuotientGroup.mk (Units.mk0 d h)) :=
    fun d h => dif_neg h
  have hsqtriv : ∀ W : (AdjoinRoot g)ˣ, QuotientGroup.mk (W ^ 2) = (1 : (AdjoinRoot g)ˣ ⧸ Rsq) := by
    intro W
    rw [QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨W, by simp [powMonoidHom_apply]⟩
  have hclass : ∀ (u : (AdjoinRoot g)ˣ) (d w : AdjoinRoot g) (hd : d ≠ 0) (hw : w ≠ 0),
      (u : AdjoinRoot g) = d * w ^ 2 →
      QuotientGroup.mk u = (QuotientGroup.mk (Units.mk0 d hd) : (AdjoinRoot g)ˣ ⧸ Rsq) := by
    intro u d w hd hw h
    rw [QuotientGroup.eq]
    refine MonoidHom.mem_range.mpr ⟨(Units.mk0 w hw)⁻¹, ?_⟩
    apply Units.ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    rw [h]
    field_simp
  -- the image lies in the finite set {0} ∪ F(D)
  have hmem : ∀ P : E.toAffine.Point,
      κ P ∈ insert (0 : Additive ((AdjoinRoot g)ˣ ⧸ Rsq)) (F '' (D : Set (AdjoinRoot g))) := by
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · show κ 0 ∈ insert (0 : Additive ((AdjoinRoot g)ˣ ⧸ Rsq)) (F '' (D : Set (AdjoinRoot g)))
      rw [map_zero]
      exact Set.mem_insert _ _
    · obtain ⟨u, hu, hκu⟩ := hκ x y h
      obtain ⟨d, hd, w, hw⟩ := hD' x y (hcurve x y h)
      have hu0 : (u : AdjoinRoot g) ≠ 0 := u.ne_zero
      have hd0 : d ≠ 0 := fun h0 => hu0 (by rw [hu, hw, h0, zero_mul])
      have hw0 : w ≠ 0 := fun h0 => hu0 (by rw [hu, hw, h0]; simp)
      right
      refine ⟨d, hd, ?_⟩
      rw [hF d hd0, hκu]
      exact congrArg Additive.ofMul (hclass u d w hd0 hw0 (hu.trans hw)).symm
  have hs : (insert (0 : Additive ((AdjoinRoot g)ˣ ⧸ Rsq)) (F '' (D : Set (AdjoinRoot g)))).Finite :=
    (D.finite_toSet.image F).insert 0
  -- the defect set: 0 and the points with y = 0 (which all have x = e)
  let Z : Set E.toAffine.Point :=
    {S | ∃ x : ℚ, ∃ h : E.toAffine.Nonsingular x 0, S = WeierstrassCurve.Affine.Point.some x 0 h}
  have hZ : Z.Subsingleton := by
    rintro S1 ⟨x1, h1, rfl⟩ S2 ⟨x2, h2, rfl⟩
    have hx : ∀ x : ℚ, ∀ h : E.toAffine.Nonsingular x 0, x = e := by
      intro x h
      have hc := hcurve x 0 h
      have h0 : (x - e) * (x ^ 2 + e * x + (e ^ 2 + p)) = 0 := by linear_combination -hc
      rcases mul_eq_zero.mp h0 with h' | h'
      · linarith
      · exact absurd h' (hgne x)
    have hx12 : x1 = x2 := (hx x1 h1).trans (hx x2 h2).symm
    subst hx12
    rfl
  have hY : (insert (0 : E.toAffine.Point) Z).Finite := (hZ.finite).insert 0
  -- kernel of κ up to the defect set
  have hfib : ∀ P Q : E.toAffine.Point, κ P = κ Q →
      ∃ d ∈ hY.toFinset, ∃ R : E.toAffine.Point, P = Q + d + 2 • R := by
    intro P Q hPQ
    obtain ⟨S, hS⟩ : ∃ S : E.toAffine.Point, S = P + -Q := ⟨_, rfl⟩
    have hκS : κ S = 0 := by
      rw [hS, map_add, map_neg, hPQ]
      exact add_neg_cancel (κ Q)
    rcases S with _ | ⟨x, y, h⟩
    · refine ⟨0, (Set.Finite.mem_toFinset hY).mpr (Set.mem_insert _ _), 0, ?_⟩
      have hPQ0 : P = Q := add_neg_eq_zero.mp hS.symm
      rw [hPQ0]
      simp
    · by_cases hy : y = 0
      · subst hy
        refine ⟨WeierstrassCurve.Affine.Point.some x 0 h,
          (Set.Finite.mem_toFinset hY).mpr (Set.mem_insert_of_mem _ ⟨x, h, rfl⟩), 0, ?_⟩
        rw [hS, nsmul_zero, add_zero]
        abel
      · obtain ⟨u, hu, hκu⟩ := hκ x y h
        rw [hκu] at hκS
        have hmk : (QuotientGroup.mk u : (AdjoinRoot g)ˣ ⧸ Rsq) = 1 := ofMul_eq_zero.mp hκS
        obtain ⟨W, hW⟩ := MonoidHom.mem_range.mp ((QuotientGroup.eq_one_iff u).mp hmk)
        have hβ : (W : AdjoinRoot g) ^ 2 = AdjoinRoot.of g x - AdjoinRoot.root g := by
          rw [← hu]
          simpa [powMonoidHom_apply] using congrArg Units.val hW
        obtain ⟨R, hR⟩ := MPP.Solutions.Bsd117.main p q e g E ha1 ha2 ha3 ha4 ha6 hcub hgdef hirr x y h hy
          (W : AdjoinRoot g) hβ
        refine ⟨0, (Set.Finite.mem_toFinset hY).mpr (Set.mem_insert _ _), R, ?_⟩
        rw [add_zero, two_nsmul, hR, hS]
        abel
  exact MPP.Solutions.Bsd113.main E.toAffine.Point (Additive ((AdjoinRoot g)ˣ ⧸ Rsq)) κ _ hY.toFinset hs hmem hfib

end MPP.Solutions.Bsd118
