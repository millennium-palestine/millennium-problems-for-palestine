import Mathlib
import MPP.Solutions.Bsd056
import MPP.Solutions.Bsd107
import MPP.Solutions.Bsd113
import MPP.Solutions.Bsd123

namespace MPP.Solutions.Bsd124

theorem main : ∀ (e1 e2 e3 : ℤ) (E : WeierstrassCurve ℚ) [E.IsElliptic], e1 + e2 + e3 = 0 → e1 ≠ e2 → e1 ≠ e3 →
    e2 ≠ e3 → E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
    E.a₄ = (e1 : ℚ) * (e2 : ℚ) + (e1 : ℚ) * (e3 : ℚ) + (e2 : ℚ) * (e3 : ℚ) →
    E.a₆ = -((e1 : ℚ) * (e2 : ℚ) * (e3 : ℚ)) →
    ∃ s : Finset E.toAffine.Point, ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro e1 e2 e3 E _ hs' h12' h13' h23' ha1 ha2 ha3 ha4 ha6
  classical
  set Rsq := (powMonoidHom (2 : ℕ) : ℚˣ →* ℚˣ).range with hRsq
  have hsQ : (e1 : ℚ) + (e2 : ℚ) + (e3 : ℚ) = 0 := by exact_mod_cast hs'
  have h12 : (e1 : ℚ) ≠ (e2 : ℚ) := by exact_mod_cast h12'
  have h13 : (e1 : ℚ) ≠ (e3 : ℚ) := by exact_mod_cast h13'
  have h23 : (e2 : ℚ) ≠ (e3 : ℚ) := by exact_mod_cast h23'
  have h21 : (e2 : ℚ) ≠ (e1 : ℚ) := fun h => h12 h.symm
  have hp1 : E.a₄ = (e1 : ℚ) * (e2 : ℚ) + (e1 : ℚ) * (e3 : ℚ) + (e2 : ℚ) * (e3 : ℚ) := ha4
  have hq1 : E.a₆ = -((e1 : ℚ) * (e2 : ℚ) * (e3 : ℚ)) := ha6
  have hp2 : E.a₄ = (e2 : ℚ) * (e1 : ℚ) + (e2 : ℚ) * (e3 : ℚ) + (e1 : ℚ) * (e3 : ℚ) := by
    rw [ha4]; ring
  have hq2 : E.a₆ = -((e2 : ℚ) * (e1 : ℚ) * (e3 : ℚ)) := by
    rw [ha6]; ring
  have hsQ2 : (e2 : ℚ) + (e1 : ℚ) + (e3 : ℚ) = 0 := by linarith
  have hc1 : ((e1 : ℚ) - (e2 : ℚ)) * ((e1 : ℚ) - (e3 : ℚ)) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)
  have hc2 : ((e2 : ℚ) - (e1 : ℚ)) * ((e2 : ℚ) - (e3 : ℚ)) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h21) (sub_ne_zero.mpr h23)
  -- the curve equation with the roots
  have hcurve : ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
      y ^ 2 = (x - (e1 : ℚ)) * (x - (e2 : ℚ)) * (x - (e3 : ℚ)) := by
    intro x y h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq + x ^ 2 * hsQ
  -- the Kummer maps of bsd-123 for the roots e1 and e2
  obtain ⟨κ1, hκ1⟩ := MPP.Solutions.Bsd123.main E.a₄ E.a₆ (e1 : ℚ) (e2 : ℚ) (e3 : ℚ) E ha1 ha2 ha3 rfl rfl
    hsQ hp1 hq1 h12 h13
  obtain ⟨κ2, hκ2⟩ := MPP.Solutions.Bsd123.main E.a₄ E.a₆ (e2 : ℚ) (e1 : ℚ) (e3 : ℚ) E ha1 ha2 ha3 rfl rfl
    hsQ2 hp2 hq2 h21 h23
  -- finite representatives from bsd-107 for x − e1 and x − e2
  obtain ⟨D1, hD1⟩ := MPP.Solutions.Bsd107.main e1 e2 e3 hs' h12' h13' h23'
  obtain ⟨D2, hD2⟩ := MPP.Solutions.Bsd107.main e2 e1 e3 (by omega) (fun h => h12' h.symm) h23' h13'
  -- helper facts about square classes
  have hcls : ∀ (a b u : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0), a = b * u ^ 2 →
      (QuotientGroup.mk (Units.mk0 a ha) : ℚˣ ⧸ Rsq) = QuotientGroup.mk (Units.mk0 b hb) := by
    intro a b u ha hb hu h
    rw [QuotientGroup.eq]
    refine MonoidHom.mem_range.mpr ⟨(Units.mk0 u hu)⁻¹, Units.ext ?_⟩
    simp [powMonoidHom_apply, h]
  have hsqroot : ∀ u : ℚˣ, Additive.ofMul (QuotientGroup.mk u : ℚˣ ⧸ Rsq) = 0 → ∃ w : ℚ, (u : ℚ) = w ^ 2 := by
    intro u hu
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff] at hu
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hu
    exact ⟨(w : ℚ), by rw [← congrArg Units.val hw]; simp [powMonoidHom_apply]⟩
  -- the finite set of values of the first Kummer map
  obtain ⟨F1, hF1fin, hF1⟩ : ∃ F1 : Set (Additive (ℚˣ ⧸ Rsq)), F1.Finite ∧
      ∀ P : E.toAffine.Point, κ1 P ∈ F1 := by
    refine ⟨({0, Additive.ofMul (QuotientGroup.mk (Units.mk0 (((e1 : ℚ) - (e2 : ℚ)) * ((e1 : ℚ) - (e3 : ℚ))) hc1))} ∪
      (fun d : ℤ => if h : (d : ℚ) = 0 then (0 : Additive (ℚˣ ⧸ Rsq)) else
        Additive.ofMul (QuotientGroup.mk (Units.mk0 (d : ℚ) h))) '' (D1 : Set ℤ)), ?_, ?_⟩
    · exact ((Set.finite_singleton _).insert _).union (D1.finite_toSet.image _)
    · intro P
      rcases P with _ | ⟨x, y, h⟩
      · exact Or.inl (by show κ1 0 ∈ _; rw [map_zero]; exact Set.mem_insert _ _)
      · by_cases hx : x = (e1 : ℚ)
        · obtain ⟨u0, hu0, hκu0⟩ := (hκ1 x y h).2 hx
          have hu0eq : u0 = Units.mk0 (((e1 : ℚ) - (e2 : ℚ)) * ((e1 : ℚ) - (e3 : ℚ))) hc1 := Units.ext hu0
          rw [hκu0, hu0eq]
          exact Or.inl (Or.inr (Set.mem_singleton _))
        · obtain ⟨u0, hu0, hκu0⟩ := (hκ1 x y h).1 hx
          obtain ⟨d, hd, u, hu⟩ := (hD1 x y (hcurve x y h)).1 hx
          have hu0ne : (u0 : ℚ) ≠ 0 := u0.ne_zero
          have hdne : (d : ℚ) ≠ 0 := by
            intro h0
            apply hu0ne
            rw [hu0, hu, h0, zero_mul]
          have hune : u ≠ 0 := by
            intro h0
            apply hu0ne
            rw [hu0, hu, h0]
            ring
          have hu0eq : u0 = Units.mk0 (x - (e1 : ℚ)) (sub_ne_zero.mpr hx) := Units.ext hu0
          rw [hκu0, hu0eq]
          refine Or.inr ⟨d, hd, ?_⟩
          simp only [dif_neg hdne]
          exact congrArg Additive.ofMul (hcls (x - (e1 : ℚ)) (d : ℚ) u (sub_ne_zero.mpr hx) hdne hune hu).symm
  -- the finite set of values of the second Kummer map
  obtain ⟨F2, hF2fin, hF2⟩ : ∃ F2 : Set (Additive (ℚˣ ⧸ Rsq)), F2.Finite ∧
      ∀ P : E.toAffine.Point, κ2 P ∈ F2 := by
    refine ⟨({0, Additive.ofMul (QuotientGroup.mk (Units.mk0 (((e2 : ℚ) - (e1 : ℚ)) * ((e2 : ℚ) - (e3 : ℚ))) hc2))} ∪
      (fun d : ℤ => if h : (d : ℚ) = 0 then (0 : Additive (ℚˣ ⧸ Rsq)) else
        Additive.ofMul (QuotientGroup.mk (Units.mk0 (d : ℚ) h))) '' (D2 : Set ℤ)), ?_, ?_⟩
    · exact ((Set.finite_singleton _).insert _).union (D2.finite_toSet.image _)
    · intro P
      rcases P with _ | ⟨x, y, h⟩
      · exact Or.inl (by show κ2 0 ∈ _; rw [map_zero]; exact Set.mem_insert _ _)
      · by_cases hx : x = (e2 : ℚ)
        · obtain ⟨u0, hu0, hκu0⟩ := (hκ2 x y h).2 hx
          have hu0eq : u0 = Units.mk0 (((e2 : ℚ) - (e1 : ℚ)) * ((e2 : ℚ) - (e3 : ℚ))) hc2 := Units.ext hu0
          rw [hκu0, hu0eq]
          exact Or.inl (Or.inr (Set.mem_singleton _))
        · obtain ⟨u0, hu0, hκu0⟩ := (hκ2 x y h).1 hx
          have hcx : y ^ 2 = (x - (e2 : ℚ)) * (x - (e1 : ℚ)) * (x - (e3 : ℚ)) := by
            rw [hcurve x y h]
            ring
          obtain ⟨d, hd, u, hu⟩ := (hD2 x y hcx).1 hx
          have hu0ne : (u0 : ℚ) ≠ 0 := u0.ne_zero
          have hdne : (d : ℚ) ≠ 0 := by
            intro h0
            apply hu0ne
            rw [hu0, hu, h0, zero_mul]
          have hune : u ≠ 0 := by
            intro h0
            apply hu0ne
            rw [hu0, hu, h0]
            ring
          have hu0eq : u0 = Units.mk0 (x - (e2 : ℚ)) (sub_ne_zero.mpr hx) := Units.ext hu0
          rw [hκu0, hu0eq]
          refine Or.inr ⟨d, hd, ?_⟩
          simp only [dif_neg hdne]
          exact congrArg Additive.ofMul (hcls (x - (e2 : ℚ)) (d : ℚ) u (sub_ne_zero.mpr hx) hdne hune hu).symm
  -- the finite set of points with y = 0
  obtain ⟨Z, hZfin, hZmem⟩ : ∃ Z : Set E.toAffine.Point, Z.Finite ∧
      ∀ (x : ℚ) (h : E.toAffine.Nonsingular x 0), WeierstrassCurve.Affine.Point.some x 0 h ∈ Z := by
    refine ⟨{S | ∃ (x : ℚ) (h : E.toAffine.Nonsingular x 0),
      S = WeierstrassCurve.Affine.Point.some x 0 h}, ?_, ?_⟩
    · apply Set.Finite.of_finite_image (f := fun S : E.toAffine.Point => match S with
        | WeierstrassCurve.Affine.Point.zero => (0 : ℚ)
        | WeierstrassCurve.Affine.Point.some x _ _ => x)
      · refine Set.Finite.subset (({(e1 : ℚ), (e2 : ℚ), (e3 : ℚ)} : Set ℚ).toFinite) ?_
        rintro _ ⟨S, ⟨x, h, rfl⟩, rfl⟩
        show x ∈ ({(e1 : ℚ), (e2 : ℚ), (e3 : ℚ)} : Set ℚ)
        have hp0 : (x - (e1 : ℚ)) * (x - (e2 : ℚ)) * (x - (e3 : ℚ)) = 0 := by
          rw [← hcurve x 0 h]
          ring
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases mul_eq_zero.mp hp0 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · left
            linarith
          · right
            left
            linarith
        · right
          right
          linarith
      · rintro S1 ⟨x1, h1, rfl⟩ S2 ⟨x2, h2, rfl⟩ heq
        have hx : x1 = x2 := heq
        subst hx
        rfl
    · intro x h
      exact ⟨x, h, rfl⟩
  -- the pair of Kummer maps
  have hmemκ : ∀ P : E.toAffine.Point, (κ1.prod κ2) P ∈ F1 ×ˢ F2 := fun P =>
    Set.mk_mem_prod (hF1 P) (hF2 P)
  have hfib : ∀ P Q : E.toAffine.Point, (κ1.prod κ2) P = (κ1.prod κ2) Q →
      ∃ d ∈ insert (0 : E.toAffine.Point) (hZfin.toFinset : Finset E.toAffine.Point),
        ∃ R : E.toAffine.Point, P = Q + d + 2 • R := by
    intro P Q hPQ
    have h1 : κ1 P = κ1 Q := congrArg Prod.fst hPQ
    have h2 : κ2 P = κ2 Q := congrArg Prod.snd hPQ
    obtain ⟨S, hS⟩ : ∃ S : E.toAffine.Point, S = P + -Q := ⟨_, rfl⟩
    have hS1 : κ1 S = 0 := by rw [hS, map_add, map_neg, h1, add_neg_cancel]
    have hS2 : κ2 S = 0 := by rw [hS, map_add, map_neg, h2, add_neg_cancel]
    rcases S with _ | ⟨x, y, h⟩
    · refine ⟨0, Finset.mem_insert_self _ _, 0, ?_⟩
      have hPQ' : P = Q := add_neg_eq_zero.mp hS.symm
      rw [hPQ']
      simp
    · by_cases hy : y = 0
      · subst hy
        refine ⟨WeierstrassCurve.Affine.Point.some x 0 h,
          Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset hZfin).mpr (hZmem x h)), 0, ?_⟩
        rw [hS]
        abel
      · have hxe1 : x ≠ (e1 : ℚ) := by
          intro hx
          apply hy
          have h0 : y ^ 2 = 0 := by
            rw [hcurve x y h, hx]
            ring
          exact pow_eq_zero_iff two_ne_zero |>.mp h0
        have hxe2 : x ≠ (e2 : ℚ) := by
          intro hx
          apply hy
          have h0 : y ^ 2 = 0 := by
            rw [hcurve x y h, hx]
            ring
          exact pow_eq_zero_iff two_ne_zero |>.mp h0
        obtain ⟨u1, hu1, hκu1⟩ := (hκ1 x y h).1 hxe1
        rw [hκu1] at hS1
        obtain ⟨w1, hw1⟩ := hsqroot u1 hS1
        obtain ⟨u2, hu2, hκu2⟩ := (hκ2 x y h).1 hxe2
        rw [hκu2] at hS2
        obtain ⟨w2, hw2⟩ := hsqroot u2 hS2
        have hx1 : x - (e1 : ℚ) = w1 ^ 2 := hu1.symm.trans hw1
        have hx2 : x - (e2 : ℚ) = w2 ^ 2 := hu2.symm.trans hw2
        have hw1ne : w1 ≠ 0 := fun h0 => hxe1 (sub_eq_zero.mp (by rw [hx1, h0]; ring))
        have hw2ne : w2 ≠ 0 := fun h0 => hxe2 (sub_eq_zero.mp (by rw [hx2, h0]; ring))
        have hw12 : (w1 * w2) ^ 2 = (x - (e1 : ℚ)) * (x - (e2 : ℚ)) := by
          rw [mul_pow, hx1, hx2]
        have hkey : y ^ 2 = (w1 * w2) ^ 2 * (x - (e3 : ℚ)) := by
          rw [hw12, hcurve x y h]
        have hA3 : (y / (w1 * w2)) ^ 2 + (e3 : ℚ) = x := by
          have hden : w1 * w2 ≠ 0 := mul_ne_zero hw1ne hw2ne
          rw [div_pow, hkey, mul_div_cancel_left₀ _ (pow_ne_zero 2 hden)]
          ring
        obtain ⟨R, hR⟩ := MPP.Solutions.Bsd056.main (e1 : ℚ) (e2 : ℚ) (e3 : ℚ) E hsQ h12 h13 h23 ha1 ha2 ha3
          hp1 hq1 x y h hy ⟨w1, w2, y / (w1 * w2), by linarith [hx1], by linarith [hx2], hA3⟩
        refine ⟨0, Finset.mem_insert_self _ _, R, ?_⟩
        rw [add_zero, two_nsmul, hR, hS]
        abel
  exact MPP.Solutions.Bsd113.main E.toAffine.Point (Additive (ℚˣ ⧸ Rsq) × Additive (ℚˣ ⧸ Rsq))
    (κ1.prod κ2) (F1 ×ˢ F2) (insert (0 : E.toAffine.Point) (hZfin.toFinset : Finset E.toAffine.Point))
    (hF1fin.prod hF2fin) hmemκ hfib

end MPP.Solutions.Bsd124
