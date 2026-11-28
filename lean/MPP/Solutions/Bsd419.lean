import Mathlib
import MPP.Solutions.Bsd411

namespace MPP.Solutions.Bsd419

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ),
    Odd m → (m : K) ≠ 0 →
    (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      (m : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      (W.preΨ' m).eval x = 0) →
    Nat.card {P : W.toAffine.Point // (m : ℤ) • P = 0} ≤ m ^ 2 := by
  intro K _ _ W _ m hodd hm hyp
  classical
  set f := W.preΨ' m with hfdef
  have hf0 : f ≠ 0 := W.preΨ'_ne_zero hm
  have hdeg : f.natDegree = (m ^ 2 - 1) / 2 := by
    rw [hfdef, W.natDegree_preΨ' hm, if_neg (Nat.not_even_iff_odd.mpr hodd)]
  have hm2 : 2 * f.natDegree + 1 = m ^ 2 := by
    have h1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hodd.pos
    have h2 : m ^ 2 % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    rw [hdeg]
    omega
  -- the affine points of the curve whose x-coordinate is a root of f
  set T : Set (K × K) := {P : K × K | P.2 ^ 2 + W.a₁ * P.1 * P.2 + W.a₃ * P.2 =
      P.1 ^ 3 + W.a₂ * P.1 ^ 2 + W.a₄ * P.1 + W.a₆ ∧ f.eval P.1 = 0} with hTdef
  have hcount : T.ncard ≤ 2 * f.natDegree :=
    MPP.Solutions.Bsd411.main K W f hf0
  -- T is finite: its x-coordinates are roots of f, and each fibre is a root set of a nonzero quadratic
  have hfin : T.Finite := by
    let F : Finset (K × K) := f.roots.toFinset.biUnion (fun x =>
      ((Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
        - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).roots.toFinset.image (fun y => (x, y))))
    have hsub : T ⊆ (F : Set (K × K)) := by
      rintro ⟨x, y⟩ ⟨hc, hfx⟩
      have hx : x ∈ f.roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0]
        exact hfx
      have hq : (Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
          - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) ≠ 0 := by
        intro h0
        have hc2 := congrArg (fun p => Polynomial.coeff p 2) h0
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_zero, Polynomial.coeff_X] at hc2
        norm_num at hc2
      have hy : y ∈ (Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
          - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
        simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
        linear_combination hc
      simp only [F, Finset.coe_biUnion, Set.mem_iUnion]
      exact ⟨x, hx, Finset.mem_image.2 ⟨y, hy, rfl⟩⟩
    exact F.finite_toSet.subset hsub
  -- the m-torsion counted through the map sending O to none and (x, y) to some (x, y)
  set Tor : Set W.toAffine.Point := {P | (m : ℤ) • P = 0} with hTor
  let g : W.toAffine.Point → Option (K × K) := fun P => match P with
    | .zero => none
    | .some x y _ => some (x, y)
  have hinj : Set.InjOn g Tor := by
    rintro (_ | ⟨x, y, hxy⟩) _ (_ | ⟨x', y', hxy'⟩) _ hg
    · rfl
    · exact absurd hg.symm (by simp [g])
    · exact absurd hg (by simp [g])
    · have hxx : x = x' := (Prod.mk.inj (Option.some.inj hg)).1
      have hyy : y = y' := (Prod.mk.inj (Option.some.inj hg)).2
      subst hxx
      subst hyy
      rfl
  have hsubI : g '' Tor ⊆ insert none (Option.some '' T) := by
    rintro _ ⟨P, hP, rfl⟩
    rcases P with _ | ⟨x, y, hxy⟩
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨(x, y), ⟨?_, ?_⟩, rfl⟩
      · have h := hxy.1
        rw [WeierstrassCurve.Affine.equation_iff] at h
        exact h
      · exact hyp x y hxy hP
  have hfinI : (insert none (Option.some '' T)).Finite := (hfin.image _).insert _
  have hnot : (none : Option (K × K)) ∉ Option.some '' T := by
    rintro ⟨w, _, h⟩
    exact Option.some_ne_none w h
  calc Nat.card {P : W.toAffine.Point // (m : ℤ) • P = 0}
      = Tor.ncard := by
        rw [← Nat.card_coe_set_eq]
        rfl
    _ = (g '' Tor).ncard := hinj.ncard_image.symm
    _ ≤ (insert none (Option.some '' T)).ncard := Set.ncard_le_ncard hsubI hfinI
    _ = (Option.some '' T).ncard + 1 := Set.ncard_insert_of_notMem hnot (hfin.image _)
    _ = T.ncard + 1 := by rw [Set.ncard_image_of_injective _ (Option.some_injective _)]
    _ ≤ 2 * f.natDegree + 1 := by omega
    _ = m ^ 2 := hm2

end MPP.Solutions.Bsd419
