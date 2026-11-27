import Mathlib

namespace MPP.Solutions.Bsd354

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (m : ℕ),
    Even m → (m : K) ≠ 0 →
    (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 →
      (W.preΨ' m).eval x = 0) →
    Nat.card {P : W.toAffine.Point // m • P = 0} ≤ m ^ 2 := by
  intro K _ _ W m hEven hm H
  classical
  by_cases hfin : Finite {P : W.toAffine.Point // m • P = 0}
  swap
  · have := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  letI := Fintype.ofFinite {P : W.toAffine.Point // m • P = 0}
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  obtain ⟨k, hk⟩ := hEven
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    apply hm
    rw [hk]
    push_cast
    linear_combination (k : K) * h
  have hm2 : 2 ≤ m := by omega
  have h4le : 4 ≤ m ^ 2 := by nlinarith
  have hmodd : m ^ 2 % 2 = 0 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨⟨k, hk⟩, two_ne_zero⟩)
  have hkey : 2 * ((m ^ 2 - 4) / 2) + 4 = m ^ 2 := by omega
  -- bsd-315: among three nonsingular points with one x-coordinate, two have equal y-coordinate
  have bsd315 : ∀ (x y₁ y₂ y₃ : K), W.toAffine.Nonsingular x y₁ → W.toAffine.Nonsingular x y₂ →
      W.toAffine.Nonsingular x y₃ → y₁ = y₂ ∨ y₁ = y₃ ∨ y₂ = y₃ := by
    intro x y₁ y₂ y₃ h₁ h₂ h₃
    have e1 := (W.toAffine.equation_iff x y₁).mp h₁.1
    have e2 := (W.toAffine.equation_iff x y₂).mp h₂.1
    have e3 := (W.toAffine.equation_iff x y₃).mp h₃.1
    by_contra h
    push_neg at h
    obtain ⟨h12, h13, h23⟩ := h
    have s12 : (y₁ - y₂) * (y₁ + y₂ + (W.a₁ * x + W.a₃)) = 0 := by linear_combination e1 - e2
    have s13 : (y₁ - y₃) * (y₁ + y₃ + (W.a₁ * x + W.a₃)) = 0 := by linear_combination e1 - e3
    have k2 : y₁ + y₂ + (W.a₁ * x + W.a₃) = 0 := (mul_eq_zero.mp s12).resolve_left (sub_ne_zero.mpr h12)
    have k3 : y₁ + y₃ + (W.a₁ * x + W.a₃) = 0 := (mul_eq_zero.mp s13).resolve_left (sub_ne_zero.mpr h13)
    exact h23 (by linear_combination k2 - k3)
  have hsome : ∀ P : W.toAffine.Point, P ≠ 0 → ∃ x y h, P = WeierstrassCurve.Affine.Point.some x y h := by
    intro P hP
    cases P with
    | zero => exact absurd rfl hP
    | some x y h => exact ⟨x, y, h, rfl⟩
  -- the x-coordinate map (zero goes to 0)
  let f : {P : W.toAffine.Point // m • P = 0} → K := fun P =>
    match P.1 with
    | .zero => 0
    | .some x _ _ => x
  have hval : ∀ (P : {P : W.toAffine.Point // m • P = 0}) (x y : K) (h : W.toAffine.Nonsingular x y),
      P.1 = WeierstrassCurve.Affine.Point.some x y h → f P = x := by
    intro P x y h e
    simp only [f, e]
  -- two-torsion: the cubic whose roots are the x-coordinates of affine two-torsion points
  let c : Polynomial K := Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C W.b₂ * Polynomial.X ^ 2 +
    Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hcdeg : c.natDegree ≤ 3 := by
    simp only [c]
    compute_degree!
  have hc3 : c.coeff 3 = 4 := by
    simp only [c]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_add]
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, Polynomial.coeff_zero] at hc3
    exact h4 hc3.symm
  have hsing : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      2 * y + W.a₁ * x + W.a₃ = 0 := by
    intro x y h hP
    rw [two_nsmul] at hP
    have e := eq_neg_of_add_eq_zero_left hP
    rw [WeierstrassCurve.Affine.Point.neg_some] at e
    injection e with _ hy
    unfold WeierstrassCurve.Affine.negY at hy
    linear_combination hy
  have hroot : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → c.eval x = 0 := by
    intro x y h hP
    have hy := hsing x y h hP
    have e := (W.toAffine.equation_iff x y).mp h.1
    simp only [c, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (2 * y + W.a₁ * x + W.a₃) * hy - 4 * e
  have hsome2 : ∀ P : {P : W.toAffine.Point // m • P = 0}, P.1 ≠ 0 →
      ∃ x y h, P.1 = WeierstrassCurve.Affine.Point.some x y h := fun P hP => hsome P.1 hP
  -- splitting the nonzero torsion points by whether they are two-torsion
  have hA : (Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 = 0)).card +
      (Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).card =
      (Finset.univ : Finset {P : W.toAffine.Point // m • P = 0}).card :=
    Finset.card_filter_add_card_filter_not _
  have hB : ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => 2 • P.1 = 0)).card +
      ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => ¬ 2 • P.1 = 0)).card =
      (Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).card :=
    Finset.card_filter_add_card_filter_not _
  have hzero : (Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  -- two-torsion part: at most 3 nonzero points
  have himg2 : ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => 2 • P.1 = 0)).image f ⊆ c.roots.toFinset := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
    have hPq := (Finset.mem_filter.mp hP).2
    obtain ⟨x, y, h, e⟩ := hsome P.1 (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2
    have h2P : 2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [← e]
      exact hPq
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc0, Polynomial.IsRoot.def, hval P x y h e]
    exact hroot x y h h2P
  have hfib2 : ∀ a ∈ ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => 2 • P.1 = 0)).image f,
      (((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
        (fun P => 2 • P.1 = 0)).filter (fun P => f P = a)).card ≤ 1 := by
    intro a _
    rw [Finset.card_le_one]
    intro p hp q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨xp, yp, hp', ep⟩ := hsome p.1 hp.1.1
    obtain ⟨xq, yq, hq', eq₀⟩ := hsome q.1 hq.1.1
    have fp := hval p xp yp hp' ep
    have fq := hval q xq yq hq' eq₀
    have hxq : xq = xp := by rw [← fq, ← fp, hq.2, hp.2]
    have hyp := hsing xp yp hp' (by rw [← ep]; exact hp.1.2)
    have hyq := hsing xq yq hq' (by rw [← eq₀]; exact hq.1.2)
    rw [hxq] at hyq
    have hy : yp = yq := by
      have h22 : 2 * (yp - yq) = 0 := by linear_combination hyp - hyq
      have h23 := (mul_eq_zero.mp h22).resolve_left h2
      linear_combination h23
    subst hxq
    subst hy
    exact Subtype.ext (by rw [ep, eq₀])
  have hn2 : ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => 2 • P.1 = 0)).card ≤ 3 := by
    have h1 := Finset.card_le_mul_card_image (f := f)
      ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
        (fun P => 2 • P.1 = 0)) 1 hfib2
    have h2' : (((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
        (fun P => 2 • P.1 = 0)).image f).card ≤ 3 := by
      calc _ ≤ c.roots.toFinset.card := Finset.card_le_card himg2
        _ ≤ Multiset.card c.roots := Multiset.toFinset_card_le _
        _ ≤ c.natDegree := Polynomial.card_roots' _
        _ ≤ 3 := hcdeg
    omega
  -- non-two-torsion part: x-coordinates are roots of preΨ' m, at most two points each
  have hf0 : W.preΨ' m ≠ 0 := W.preΨ'_ne_zero hm
  have hdeg : (W.preΨ' m).natDegree = (m ^ 2 - 4) / 2 := by
    rw [W.natDegree_preΨ' hm, if_pos ⟨k, hk⟩]
  have himgn : ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => ¬ 2 • P.1 = 0)).image f ⊆ (W.preΨ' m).roots.toFinset := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
    have hPn := (Finset.mem_filter.mp hP).2
    obtain ⟨x, y, h, e⟩ := hsome P.1 (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2
    have hmP : m • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [← e]
      exact P.2
    have h2P : 2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 := by
      rw [← e]
      exact hPn
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hval P x y h e]
    exact H x y h hmP h2P
  have hfibn : ∀ a ∈ ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => ¬ 2 • P.1 = 0)).image f,
      (((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
        (fun P => ¬ 2 • P.1 = 0)).filter (fun P => f P = a)).card ≤ 2 := by
    intro a _
    by_contra hc
    push_neg at hc
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.mp hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq hr
    obtain ⟨xp, yp, hp', ep⟩ := hsome p.1 hp.1.1
    obtain ⟨xq, yq, hq', eq₀⟩ := hsome q.1 hq.1.1
    obtain ⟨xr, yr, hr', er⟩ := hsome r.1 hr.1.1
    have fp := hval p xp yp hp' ep
    have fq := hval q xq yq hq' eq₀
    have fr := hval r xr yr hr' er
    have ha1 : xp = a := by rw [← fp]; exact hp.2
    have ha2 : xq = a := by rw [← fq]; exact hq.2
    have ha3 : xr = a := by rw [← fr]; exact hr.2
    have hxq : xq = xp := ha2.trans ha1.symm
    have hxr : xr = xp := ha3.trans ha1.symm
    subst hxq hxr
    rcases bsd315 _ yp yq yr hp' hq' hr' with h | h | h
    · subst h
      exact hpq (Subtype.ext (by rw [ep, eq₀]))
    · subst h
      exact hpr (Subtype.ext (by rw [ep, er]))
    · subst h
      exact hqr (Subtype.ext (by rw [eq₀, er]))
  have hnn : ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
      (fun P => ¬ 2 • P.1 = 0)).card ≤ 2 * ((m ^ 2 - 4) / 2) := by
    have h1 := Finset.card_le_mul_card_image (f := f)
      ((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
        (fun P => ¬ 2 • P.1 = 0)) 2 hfibn
    have h2' : (((Finset.univ.filter (fun P : {P : W.toAffine.Point // m • P = 0} => P.1 ≠ 0)).filter
        (fun P => ¬ 2 • P.1 = 0)).image f).card ≤ (m ^ 2 - 4) / 2 := by
      calc _ ≤ (W.preΨ' m).roots.toFinset.card := Finset.card_le_card himgn
        _ ≤ Multiset.card (W.preΨ' m).roots := Multiset.toFinset_card_le _
        _ ≤ (W.preΨ' m).natDegree := Polynomial.card_roots' _
        _ = (m ^ 2 - 4) / 2 := hdeg
    calc _ ≤ 2 * _ := h1
      _ ≤ 2 * ((m ^ 2 - 4) / 2) := Nat.mul_le_mul_left 2 h2'
  omega

end MPP.Solutions.Bsd354
