import Mathlib
import MPP.Solutions.Bsd072
import MPP.Solutions.Bsd124
import MPP.Solutions.Bsd126

namespace MPP.Solutions.Bsd128

theorem main : ∀ (p q e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e1 + e2 + e3 = 0 → p = e1 * e2 + e1 * e3 + e2 * e3 → q = -(e1 * e2 * e3) →
    e1 ≠ e2 → e1 ≠ e3 → e2 ≠ e3 →
    ∃ s : Finset E.toAffine.Point, ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro p q e1 e2 e3 E _ ha1 ha2 ha3 ha4 ha6 hs hp hq h12 h13 h23
  classical
  -- scale to a curve with integer roots, by a rational change of variables
  obtain ⟨C, f1, f2, f3, hsum, h12', h13', h23', ha1', ha2', ha3', ha4', ha6'⟩ :=
    MPP.Solutions.Bsd126.main p q e1 e2 e3 E ha1 ha2 ha3 ha4 ha6 hs hp hq h12 h13 h23
  haveI : (C • E).IsElliptic := inferInstance
  -- the integer-root case on the scaled curve
  obtain ⟨s', hs'⟩ := MPP.Solutions.Bsd124.main f1 f2 f3 (C • E) hsum h12' h13' h23' ha1' ha2' ha3' ha4' ha6'
  -- transport along the group isomorphism of the change of variables
  obtain ⟨f, hfb, hfadd⟩ := MPP.Solutions.Bsd072.main E C
  let g : E.toAffine.Point ≃+ (C • E).toAffine.Point := AddEquiv.ofBijective (AddMonoidHom.mk' f hfadd) hfb
  refine ⟨s'.image g.symm, fun P => ?_⟩
  obtain ⟨Q', hQ', R', hR'⟩ := hs' (g P)
  refine ⟨g.symm Q', Finset.mem_image_of_mem _ hQ', g.symm R', ?_⟩
  calc P = g.symm (g P) := (g.symm_apply_apply P).symm
    _ = g.symm (Q' + 2 • R') := by rw [hR']
    _ = g.symm Q' + 2 • g.symm R' := by rw [map_add, map_nsmul]

end MPP.Solutions.Bsd128
