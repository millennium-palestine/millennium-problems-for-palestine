import Mathlib

namespace MPP.Solutions.Bsd353

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K), (2 : K) ≠ 0 →
    Nat.card {P : W.toAffine.Point // 2 • P = 0} ≤ 4 := by
  intro K _ _ W h2
  classical
  by_cases hfin : Finite {P : W.toAffine.Point // 2 • P = 0}
  swap
  · have := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  letI := Fintype.ofFinite {P : W.toAffine.Point // 2 • P = 0}
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  -- the cubic whose roots are the x-coordinates of the affine two-torsion points
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
  -- on a two-torsion point, 2y + a1 x + a3 = 0 and the cubic vanishes at x
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
  -- the x-coordinate map on the nonzero two-torsion points
  let f : {P : W.toAffine.Point // 2 • P = 0} → K := fun P =>
    match P.1 with
    | .zero => 0
    | .some x _ _ => x
  have hval : ∀ (P : {P : W.toAffine.Point // 2 • P = 0}) (x y : K) (h : W.toAffine.Nonsingular x y),
      P.1 = WeierstrassCurve.Affine.Point.some x y h → f P = x := by
    intro P x y h e
    simp only [f, e]
  have hsome : ∀ P : W.toAffine.Point, P ≠ 0 → ∃ x y h, P = WeierstrassCurve.Affine.Point.some x y h := by
    intro P hP
    cases P with
    | zero => exact absurd rfl hP
    | some x y h => exact ⟨x, y, h, rfl⟩
  have himg : (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)).image f ⊆
      c.roots.toFinset := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x, y, h, e⟩ := hsome P.1 (Finset.mem_filter.mp hP).2
    have h2P : 2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [← e]
      exact P.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc0, Polynomial.IsRoot.def, hval P x y h e]
    exact hroot x y h h2P
  -- the fibre over an x-coordinate has at most one nonzero two-torsion point
  have hfib : ∀ a ∈ (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)).image f,
      ((Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)).filter
        (fun P => f P = a)).card ≤ 1 := by
    intro a _
    rw [Finset.card_le_one]
    intro p hp q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨xp, yp, hp', ep⟩ := hsome p.1 hp.1
    obtain ⟨xq, yq, hq', eq₀⟩ := hsome q.1 hq.1
    have fp := hval p xp yp hp' ep
    have fq := hval q xq yq hq' eq₀
    have hxq : xq = xp := by rw [← fq, ← fp, hq.2, hp.2]
    have hyp := hsing xp yp hp' (by rw [← ep]; exact p.2)
    have hyq := hsing xq yq hq' (by rw [← eq₀]; exact q.2)
    rw [hxq] at hyq
    have hy : yp = yq := by
      have h22 : 2 * (yp - yq) = 0 := by linear_combination hyp - hyq
      have h23 := (mul_eq_zero.mp h22).resolve_left h2
      linear_combination h23
    subst hxq
    subst hy
    exact Subtype.ext (by rw [ep, eq₀])
  -- counting
  have hsplit : (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 = 0)).card +
      (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)).card =
      (Finset.univ : Finset {P : W.toAffine.Point // 2 • P = 0}).card :=
    Finset.card_filter_add_card_filter_not _
  have hzero : (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  have hnz : (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)).card ≤ 3 := by
    have h1 := Finset.card_le_mul_card_image (f := f)
      (Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)) 1 hfib
    have h2' : ((Finset.univ.filter (fun P : {P : W.toAffine.Point // 2 • P = 0} => P.1 ≠ 0)).image f).card ≤ 3 := by
      calc _ ≤ c.roots.toFinset.card := Finset.card_le_card himg
        _ ≤ Multiset.card c.roots := Multiset.toFinset_card_le _
        _ ≤ c.natDegree := Polynomial.card_roots' _
        _ ≤ 3 := hcdeg
    omega
  omega

end MPP.Solutions.Bsd353
