import Mathlib
import MPP.Solutions.Bsd217
import MPP.Solutions.Bsd243
import MPP.Solutions.Bsd246
import MPP.Solutions.Bsd275
import MPP.Solutions.Bsd276

namespace MPP.Solutions.Bsd302

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic],
    (2 : K) ≠ 0 → (3 : K) ≠ 0 → (5 : K) ≠ 0 → Squarefree (W.preΨ' 5) →
    25 ≤ Nat.card {P : W.toAffine.Point // (5 : ℤ) • P = 0} := by
  intro K _ _ _ W _ h2 h3 h5 hsq
  classical
  -- the 5-division polynomial has degree 12
  have hdeg : (W.preΨ' 5).natDegree = 12 := by
    rw [W.natDegree_preΨ' (n := 5) (by exact_mod_cast h5)]
    norm_num [Nat.even_iff]
  have hf0 : W.preΨ' 5 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  -- squarefree gives twelve distinct roots
  have hsep : (W.preΨ' 5).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hcard : (W.preΨ' 5).roots.toFinset.card = 12 := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hdeg]
  set R := (W.preΨ' 5).roots.toFinset with hRdef
  have hmem : ∀ x, x ∈ R ↔ (W.preΨ' 5).eval x = 0 := by
    intro x
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_roots hf0]
    exact Iff.rfl
  -- the 5-division polynomial in terms of the 3- and 4-division polynomials
  have hev : ∀ x : K, (W.preΨ' 5).eval x =
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 -
        (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3 := by
    intro x
    have hodd := W.preΨ'_odd 0
    norm_num at hodd
    rw [hodd]
    simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃]
  -- at a root, the 3-division value is nonzero (bsd-276)
  have hψ : ∀ x, (W.preΨ' 5).eval x = 0 →
      3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ ≠ 0 :=
    fun x hx h0 => MPP.Solutions.Bsd276.main K W x h2 h3 h5 h0 hx
  -- choose a nonsingular point over each root (bsd-243)
  have hlift : ∀ x ∈ R, ∃ y : K, W.toAffine.Nonsingular x y :=
    fun x _ => MPP.Solutions.Bsd243.main K W x h2
  choose! Y hY using hlift
  -- over a root, 2y + a₁x + a₃ ≠ 0: otherwise Ψ₂Sq(x) = 0 and ψ₅(x) = −Ψ₃(x)³
  have hD : ∀ x ∈ R, 2 * Y x + W.a₁ * x + W.a₃ ≠ 0 := by
    intro x hx hz
    have hE : Y x ^ 2 + W.a₁ * x * Y x + W.a₃ * Y x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
      have hx' := (hY x hx).1
      rw [WeierstrassCurve.Affine.equation_iff] at hx'
      exact hx'
    have hsq2 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
      have e : (2 * Y x + W.a₁ * x + W.a₃) ^ 2 =
          4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        linear_combination 4 * hE
      rw [← e, hz]
      ring
    have hroot := (hmem x).mp hx
    rw [hev x, hsq2] at hroot
    have h3' : (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3 = 0 := by
      linear_combination -hroot
    exact hψ x ((hmem x).mp hx) (pow_eq_zero_iff (by norm_num) |>.mp h3')
  -- the chosen affine point over each root
  obtain ⟨P0, hP0⟩ : ∃ P0 : K → W.toAffine.Point, ∀ x (hx : x ∈ R),
      P0 x = WeierstrassCurve.Affine.Point.some x (Y x) (hY x hx) :=
    ⟨fun x => if hx : x ∈ R then WeierstrassCurve.Affine.Point.some x (Y x) (hY x hx) else 0,
      fun x hx => dif_pos hx⟩
  -- it is five-torsion (bsd-275)
  have hP5 : ∀ x (hx : x ∈ R), (5 : ℤ) • P0 x = 0 := by
    intro x hx
    rw [hP0 x hx]
    exact MPP.Solutions.Bsd275.main K W x (Y x) (hY x hx) (hD x hx)
      (hψ x ((hmem x).mp hx)) ((hmem x).mp hx)
  have hP0ne : ∀ x (hx : x ∈ R), P0 x ≠ 0 := by
    intro x hx
    rw [hP0 x hx]
    exact WeierstrassCurve.Affine.Point.some_ne_zero (hY x hx)
  -- equal or opposite chosen points have equal x-coordinates
  have hA : ∀ x1 x2 (_ : x1 ∈ R) (_ : x2 ∈ R), P0 x1 = P0 x2 → x1 = x2 ∧ Y x1 = Y x2 := by
    intro x1 x2 h1 h2' heq
    rw [hP0 x1 h1, hP0 x2 h2', WeierstrassCurve.Affine.Point.some.injEq] at heq
    exact heq
  have hB : ∀ x1 x2 (_ : x1 ∈ R) (_ : x2 ∈ R), P0 x1 = -P0 x2 →
      x1 = x2 ∧ Y x1 = W.toAffine.negY x2 (Y x2) := by
    intro x1 x2 h1 h2' heq
    rw [hP0 x1 h1, hP0 x2 h2', WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq] at heq
    exact heq
  -- the five-torsion points: zero, and ±P0 x over the twelve roots
  set F : Finset W.toAffine.Point := insert 0 ((R ×ˢ (Finset.univ : Finset Bool)).image
      (fun q : K × Bool => if q.2 = true then P0 q.1 else -P0 q.1)) with hFdef
  have hF5 : ∀ P : W.toAffine.Point, (5 : ℤ) • P = 0 ↔ P ∈ F := by
    intro P
    constructor
    · intro hP
      rcases P with _ | ⟨x, y, h⟩
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have hxR : x ∈ R := (hmem x).mpr (MPP.Solutions.Bsd246.main K W x y h hP)
        rcases MPP.Solutions.Bsd217.main K W x y (Y x) h (hY x hxR) with hs | hs
        · rw [Finset.mem_image]
          refine ⟨(x, true), Finset.mem_product.mpr ⟨hxR, Finset.mem_univ _⟩, ?_⟩
          show (if true = true then P0 x else -P0 x) = _
          rw [if_pos rfl, hP0 x hxR]
          exact hs.symm
        · rw [Finset.mem_image]
          refine ⟨(x, false), Finset.mem_product.mpr ⟨hxR, Finset.mem_univ _⟩, ?_⟩
          show (if false = true then P0 x else -P0 x) = _
          rw [if_neg Bool.false_ne_true, hP0 x hxR]
          exact hs.symm
    · intro hP
      rcases Finset.mem_insert.mp hP with h0 | hmem'
      · rw [h0, smul_zero]
      · obtain ⟨q, hq, hqP⟩ := Finset.mem_image.mp hmem'
        obtain ⟨hxR, -⟩ := Finset.mem_product.mp hq
        rw [← hqP]
        show (5 : ℤ) • (if q.2 = true then P0 q.1 else -P0 q.1) = 0
        by_cases hb : q.2 = true
        · rw [if_pos hb]
          exact hP5 q.1 hxR
        · rw [if_neg hb, smul_neg, hP5 q.1 hxR, neg_zero]
  -- the map from twelve roots times two signs is injective
  have hinj : Set.InjOn (fun q : K × Bool => if q.2 = true then P0 q.1 else -P0 q.1)
      ↑(R ×ˢ (Finset.univ : Finset Bool)) := by
    rintro ⟨x1, b1⟩ hq1 ⟨x2, b2⟩ hq2 heq
    obtain ⟨h1, -⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq1)
    obtain ⟨h2', -⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq2)
    rcases b1 with _ | _ <;> rcases b2 with _ | _
    · have e : -P0 x1 = -P0 x2 := heq
      obtain ⟨hx, -⟩ := hA x1 x2 h1 h2' (neg_inj.mp e)
      subst hx
      rfl
    · have e : -P0 x1 = P0 x2 := heq
      obtain ⟨hx, hy⟩ := hB x2 x1 h2' h1 e.symm
      subst hx
      exfalso
      apply hD _ h2'
      rw [WeierstrassCurve.Affine.negY] at hy
      linear_combination hy
    · have e : P0 x1 = -P0 x2 := heq
      obtain ⟨hx, hy⟩ := hB x1 x2 h1 h2' e
      subst hx
      exfalso
      apply hD _ h1
      rw [WeierstrassCurve.Affine.negY] at hy
      linear_combination hy
    · have e : P0 x1 = P0 x2 := heq
      obtain ⟨hx, -⟩ := hA x1 x2 h1 h2' e
      subst hx
      rfl
  -- the zero point is not in the image, so F has 1 + 2 · 12 = 25 elements
  have hcardF : 25 ≤ F.card := by
    have hnot : (0 : W.toAffine.Point) ∉ (R ×ˢ (Finset.univ : Finset Bool)).image
        (fun q : K × Bool => if q.2 = true then P0 q.1 else -P0 q.1) := by
      intro h0
      obtain ⟨q, hq, hqP⟩ := Finset.mem_image.mp h0
      obtain ⟨hxR, -⟩ := Finset.mem_product.mp hq
      have hqP' : (if q.2 = true then P0 q.1 else -P0 q.1) = 0 := hqP
      by_cases hb : q.2 = true
      · rw [if_pos hb] at hqP'
        exact hP0ne _ hxR hqP'
      · rw [if_neg hb, neg_eq_zero] at hqP'
        exact hP0ne _ hxR hqP'
    rw [hFdef, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
      Finset.card_product, hcard, Finset.card_univ, Fintype.card_bool]
  have hS : Nat.card {P : W.toAffine.Point // (5 : ℤ) • P = 0} = F.card := by
    rw [← Nat.card_eq_finsetCard F]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF5)
  rw [hS]
  exact hcardF

end MPP.Solutions.Bsd302
