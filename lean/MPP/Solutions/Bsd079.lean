import Mathlib
import MPP.Solutions.Bsd069
import MPP.Solutions.Bsd072

namespace MPP.Solutions.Bsd079

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    (∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic] (p q : ℚ), E'.a₁ = 0 → E'.a₂ = 0 → E'.a₃ = 0 →
        E'.a₄ = p → E'.a₆ = q →
        ∃ s : Finset E'.toAffine.Point, ∀ P : E'.toAffine.Point, ∃ Q ∈ s, ∃ R : E'.toAffine.Point, P = Q + 2 • R) →
      ∃ s : Finset E.toAffine.Point, ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro E _ hshort
  obtain ⟨p, q, C, h1, h2, h3, h4, h6⟩ := MPP.Solutions.Bsd069.main E
  obtain ⟨f, hbij, hadd⟩ := MPP.Solutions.Bsd072.main E C
  obtain ⟨s', hs'⟩ := hshort (C • E) p q h1 h2 h3 h4 h6
  let e : E.toAffine.Point ≃ (C • E).toAffine.Point := Equiv.ofBijective f hbij
  let F : E.toAffine.Point →+ (C • E).toAffine.Point := AddMonoidHom.mk' f hadd
  have hfe : ∀ x, f (e.symm x) = x := fun x => Equiv.ofBijective_apply_symm_apply f hbij x
  refine ⟨s'.map e.symm.toEmbedding, ?_⟩
  intro P
  obtain ⟨Q', hQ', R', hPQ⟩ := hs' (f P)
  refine ⟨e.symm Q', Finset.mem_map.mpr ⟨Q', hQ', rfl⟩, e.symm R', ?_⟩
  have k1 : f (e.symm Q' + 2 • e.symm R') = f (e.symm Q') + 2 • f (e.symm R') := by
    show F (e.symm Q' + 2 • e.symm R') = F (e.symm Q') + 2 • F (e.symm R')
    rw [map_add, map_nsmul]
  apply hbij.1
  rw [k1, hfe, hfe]
  exact hPQ

end MPP.Solutions.Bsd079
