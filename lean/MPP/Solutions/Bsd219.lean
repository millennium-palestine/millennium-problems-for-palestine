import Mathlib

namespace MPP.Solutions.Bsd219

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ),
    Odd m → (m : K) ≠ 0 →
    (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → (W.preΨ' m).eval x = 0) →
    (Nat.card {P : W.toAffine.Point // m • P = 0} : ℤ) ≤ (m : ℤ) ^ 2 := by
  intro K _ _ W _ m hodd hm hcrux
  classical
  -- root count of the division polynomial (as in bsd-216)
  have hne : W.preΨ' m ≠ 0 := W.preΨ'_ne_zero hm
  have hroots : (W.preΨ' m).roots.toFinset.card ≤ (m ^ 2 - 1) / 2 := by
    have hdeg : (W.preΨ' m).natDegree = (m ^ 2 - if Even m then 4 else 1) / 2 :=
      W.natDegree_preΨ' hm
    have hodd' : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
    calc (W.preΨ' m).roots.toFinset.card
        ≤ Multiset.card (W.preΨ' m).roots := Multiset.toFinset_card_le _
      _ ≤ (W.preΨ' m).natDegree := Polynomial.card_roots' _
      _ = (m ^ 2 - 1) / 2 := by rw [hdeg, if_neg hodd']
  set T : Finset K := (W.preΨ' m).roots.toFinset with hT
  -- the x-coordinate, with the point at infinity sent to none
  let f : W.toAffine.Point → Option K := fun P => match P with
    | WeierstrassCurve.Affine.Point.zero => none
    | WeierstrassCurve.Affine.Point.some x _ _ => some x
  -- two points with the same x-coordinate are equal or opposite (as in bsd-217)
  have key : ∀ P Q : W.toAffine.Point, f P = f Q → Q = P ∨ Q = -P := by
    intro P Q h
    cases P with
    | zero =>
      cases Q with
      | zero => exact Or.inl rfl
      | @some x y hy => simp [f] at h
    | @some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp [f] at h
      | @some x₂ y₂ h₂ =>
        simp only [f, Option.some.injEq] at h
        subst h
        have e₁ := (WeierstrassCurve.Affine.equation_iff (W := W) x₁ y₁).mp h₁.1
        have e₂ := (WeierstrassCurve.Affine.equation_iff (W := W) x₁ y₂).mp h₂.1
        have hfac : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) = 0 := by
          linear_combination e₁ - e₂
        rcases mul_eq_zero.mp hfac with h' | h'
        · left
          have : y₂ = y₁ := (sub_eq_zero.mp h').symm
          subst this
          rfl
        · right
          rw [WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨rfl, by rw [WeierstrassCurve.Affine.negY]; linear_combination h'⟩
  -- the m-torsion is finite: fibres of f are at most two points
  have hSfin : {P : W.toAffine.Point | m • P = 0}.Finite := by
    apply Set.Finite.of_finite_fibers f
    · apply Set.Finite.subset ((Set.finite_singleton none).union ((T.finite_toSet).image some))
      rintro _ ⟨P, hP, rfl⟩
      cases P with
      | zero => exact Or.inl rfl
      | @some x y h =>
        right
        refine ⟨x, ?_, rfl⟩
        rw [Finset.mem_coe, hT, Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact Polynomial.IsRoot.def.mpr (hcrux x y h hP)
    · rintro b ⟨P0, hP0, rfl⟩
      apply Set.Finite.subset (Set.toFinite ({P0, -P0} : Set W.toAffine.Point))
      rintro Q ⟨hQ, hfQ⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hfQ
      rcases key P0 Q hfQ.symm with h | h
      · simp [h]
      · simp [h]
  -- counting
  set s := hSfin.toFinset with hs
  have hmem : ∀ P, P ∈ s ↔ m • P = 0 := by
    intro P
    rw [hs, Set.Finite.mem_toFinset]
    rfl
  have h0 : (0 : W.toAffine.Point) ∈ s := (hmem 0).mpr (smul_zero m)
  have hcard_s : s.card = (s.erase 0).card + 1 := (Finset.card_erase_add_one h0).symm
  set s' := s.erase 0 with hs'
  have hmem' : ∀ P, P ∈ s' → P ≠ 0 ∧ m • P = 0 := by
    intro P hP
    rw [hs', Finset.mem_erase, hmem] at hP
    exact hP
  have hfib : ∀ b ∈ s'.image f, (s'.filter (fun a => f a = b)).card ≤ 2 := by
    intro b hb
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hb
    have hsub : s'.filter (fun a => f a = f P0) ⊆ ({P0, -P0} : Finset W.toAffine.Point) := by
      intro Q hQ
      rw [Finset.mem_filter] at hQ
      rcases key P0 Q hQ.2.symm with h | h
      · simp [h]
      · simp [h]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have himg : s'.image f ⊆ T.image some := by
    intro b hb
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hP0, hPt⟩ := hmem' P hP
    cases P with
    | zero => exact absurd rfl hP0
    | @some x y h =>
      rw [Finset.mem_image]
      refine ⟨x, ?_, rfl⟩
      rw [hT, Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact Polynomial.IsRoot.def.mpr (hcrux x y h hPt)
  have hcard' : s'.card ≤ 2 * (s'.image f).card := Finset.card_le_mul_card_image s' 2 hfib
  have hcard_img : (s'.image f).card ≤ T.card :=
    (Finset.card_le_card himg).trans Finset.card_image_le
  have hN : Nat.card {P : W.toAffine.Point // m • P = 0} = s.card := by
    have e : Nat.card {P : W.toAffine.Point // m • P = 0} =
        Nat.card ↥{P : W.toAffine.Point | m • P = 0} := rfl
    rw [e, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hSfin]
  have hodd2 : m ^ 2 % 2 = 1 := Nat.odd_iff.mp hodd.pow
  have hpos : 0 < m ^ 2 := pow_pos hodd.pos 2
  have hnat : Nat.card {P : W.toAffine.Point // m • P = 0} ≤ m ^ 2 := by
    omega
  exact_mod_cast hnat

end MPP.Solutions.Bsd219
