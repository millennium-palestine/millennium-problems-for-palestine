import Mathlib

namespace MPP.Solutions.Bsd316

-- three nonsingular points over one x-coordinate have two equal y-coordinates
lemma two_y {K : Type} [Field K] (W : WeierstrassCurve K) (x y₁ y₂ y₃ : K)
    (h₁ : W.toAffine.Nonsingular x y₁) (h₂ : W.toAffine.Nonsingular x y₂)
    (h₃ : W.toAffine.Nonsingular x y₃) : y₁ = y₂ ∨ y₁ = y₃ ∨ y₂ = y₃ := by
  have e₁ := (WeierstrassCurve.Affine.equation_iff ..).mp h₁.left
  have e₂ := (WeierstrassCurve.Affine.equation_iff ..).mp h₂.left
  have e₃ := (WeierstrassCurve.Affine.equation_iff ..).mp h₃.left
  by_contra hne
  have h12 : y₁ ≠ y₂ := fun h => hne (Or.inl h)
  have h13 : y₁ ≠ y₃ := fun h => hne (Or.inr (Or.inl h))
  have h23 : y₂ ≠ y₃ := fun h => hne (Or.inr (Or.inr h))
  have k₁₂ : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x + W.a₃) = 0 := by linear_combination e₁ - e₂
  have k₁₃ : (y₁ - y₃) * (y₁ + y₃ + W.a₁ * x + W.a₃) = 0 := by linear_combination e₁ - e₃
  have s₁₂ : y₁ + y₂ + W.a₁ * x + W.a₃ = 0 := (mul_eq_zero.mp k₁₂).resolve_left (sub_ne_zero.mpr h12)
  have s₁₃ : y₁ + y₃ + W.a₁ * x + W.a₃ = 0 := (mul_eq_zero.mp k₁₃).resolve_left (sub_ne_zero.mpr h13)
  exact h23 (by linear_combination s₁₂ - s₁₃)

-- the root count of bsd-314
lemma card_le_roots {K : Type} [Field K] (W : WeierstrassCurve K) (m : ℕ) (hm : Odd m)
    (hm0 : (m : K) ≠ 0) (S : Finset K) (hS : ∀ x ∈ S, (W.preΨ' m).eval x = 0) :
    S.card ≤ (m ^ 2 - 1) / 2 := by
  classical
  have hne : W.preΨ' m ≠ 0 := W.preΨ'_ne_zero hm0
  have hsub : S ⊆ (W.preΨ' m).roots.toFinset := fun x hx => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact hS x hx
  have hodd : ¬ Even m := Nat.not_even_iff_odd.mpr hm
  calc S.card ≤ (W.preΨ' m).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (W.preΨ' m).roots := Multiset.toFinset_card_le _
    _ ≤ (W.preΨ' m).natDegree := Polynomial.card_roots' _
    _ = (m ^ 2 - 1) / 2 := by
      rw [W.natDegree_preΨ' hm0, if_neg hodd]

-- fibre counting
lemma card_le_mul_of_fibres {α β : Type} [DecidableEq β] (s : Finset α) (f : α → β)
    (T : Finset β) (hT : ∀ a ∈ s, f a ∈ T) (n : ℕ)
    (hn : ∀ b ∈ T, (s.filter fun a => f a = b).card ≤ n) : s.card ≤ n * T.card := by
  calc s.card = ∑ b ∈ T, (s.filter fun a => f a = b).card := Finset.card_eq_sum_card_fiberwise hT
    _ ≤ ∑ _b ∈ T, n := Finset.sum_le_sum hn
    _ = n * T.card := by simp [mul_comm]

-- the x-coordinate of a point (zero goes to 0; only used off zero)
def xc {K : Type} [Field K] (W : WeierstrassCurve K) : W.toAffine.Point → K
  | .zero => 0
  | .some x _ _ => x

-- two points with equal coordinates are equal
lemma some_eq_of {K : Type} [Field K] (W : WeierstrassCurve K) {x₁ x₂ y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

-- at most two nonzero points over one x-coordinate
lemma fibre_two {K : Type} [Field K] (W : WeierstrassCurve K) (b : K) (P Q S : W.toAffine.Point)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0) (hxP : xc W P = b) (hxQ : xc W Q = b) (hxS : xc W S = b)
    (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) : False := by
  cases P with
  | zero => exact hP rfl
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero => exact hQ rfl
  | some x₂ y₂ h₂ =>
  cases S with
  | zero => exact hS rfl
  | some x₃ y₃ h₃ =>
  have e₁ : x₁ = b := hxP
  have e₂ : x₂ = b := hxQ
  have e₃ : x₃ = b := hxS
  have h₁' : W.toAffine.Nonsingular b y₁ := e₁ ▸ h₁
  have h₂' : W.toAffine.Nonsingular b y₂ := e₂ ▸ h₂
  have h₃' : W.toAffine.Nonsingular b y₃ := e₃ ▸ h₃
  rcases two_y W b y₁ y₂ y₃ h₁' h₂' h₃' with h | h | h
  · exact hPQ (some_eq_of W h₁ h₂ (e₁.trans e₂.symm) h)
  · exact hPS (some_eq_of W h₁ h₃ (e₁.trans e₃.symm) h)
  · exact hQS (some_eq_of W h₂ h₃ (e₂.trans e₃.symm) h)

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (m : ℕ),
    Odd m → (m : K) ≠ 0 →
    (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → (W.preΨ' m).eval x = 0) →
    (Nat.card {P : W.toAffine.Point // m • P = 0} : ℤ) ≤ (m : ℤ) ^ 2 := by
  intro K _ _ W m hm hm0 H
  classical
  by_cases hfin : Finite {P : W.toAffine.Point // m • P = 0}
  · haveI := Fintype.ofFinite {P : W.toAffine.Point // m • P = 0}
    rw [Nat.card_eq_fintype_card]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset {P : W.toAffine.Point // m • P = 0})) (fun P => P.1 ≠ 0)
    -- the zero point is the only point outside the nonzero part
    have hzero : (Finset.univ.filter fun P : {P : W.toAffine.Point // m • P = 0} => ¬ (P.1 ≠ 0)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha hb
      exact Subtype.ext (ha.trans hb.symm)
    -- the nonzero torsion points map to roots of the division polynomial
    have hmaps : ∀ P ∈ (Finset.univ.filter fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0),
        xc W P.1 ∈ (W.preΨ' m).roots.toFinset := by
      intro P hP
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.preΨ'_ne_zero hm0)]
      rcases hPt : P.1 with _ | ⟨x, y, h⟩
      · exact absurd hPt hP
      · have hx := H x y h (by rw [← hPt]; exact P.2)
        simpa [xc, hPt] using hx
    -- at most two nonzero torsion points over each root
    have hfib : ∀ b ∈ (W.preΨ' m).roots.toFinset,
        ((Finset.univ.filter fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0).filter
          fun P => xc W P.1 = b).card ≤ 2 := by
      intro b _
      by_contra hlt
      obtain ⟨P, hP, Q, hQ, S, hS, hPQ, hPS, hQS⟩ := Finset.two_lt_card.mp (not_le.mp hlt)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP hQ hS
      exact fibre_two W b P.1 Q.1 S.1 hP.1 hQ.1 hS.1 hP.2 hQ.2 hS.2
        (fun h => hPQ (Subtype.ext h)) (fun h => hPS (Subtype.ext h)) (fun h => hQS (Subtype.ext h))
    have hnz := card_le_mul_of_fibres _ (fun P : {P : W.toAffine.Point // m • P = 0} => xc W P.1) _ hmaps 2 hfib
    -- the roots are at most (m^2 - 1)/2 in number
    have hR : (W.preΨ' m).roots.toFinset.card ≤ (m ^ 2 - 1) / 2 := by
      apply card_le_roots W m hm hm0
      intro x hx
      exact (Polynomial.mem_roots (W.preΨ'_ne_zero hm0)).mp (Multiset.mem_toFinset.mp hx)
    have hodd2 : m ^ 2 % 2 = 1 := Nat.odd_iff.mp hm.pow
    have hpos : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
    have key : Fintype.card {P : W.toAffine.Point // m • P = 0} ≤ m ^ 2 := by
      rw [← Finset.card_univ]
      generalize m ^ 2 = t at *
      omega
    exact_mod_cast key
  · haveI := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    positivity

end MPP.Solutions.Bsd316
