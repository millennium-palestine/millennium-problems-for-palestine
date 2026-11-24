import Mathlib

namespace MPP.Solutions.Bsd074

open Polynomial

theorem main : ∀ (p q : ℚ) (f : Polynomial ℚ), f = Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q →
    Irreducible f → ∀ x y : ℚ, y ^ 2 = x ^ 3 + p * x + q →
      Algebra.norm ℚ (algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f) = y ^ 2 := by
  intro p q f hf hirr x y hxy
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  let b := AdjoinRoot.powerBasis hf0
  have hgen : b.gen = AdjoinRoot.root f := AdjoinRoot.powerBasis_gen hf0
  have hchar : (Algebra.leftMulMatrix b.basis b.gen).charpoly = f := by
    rw [charpoly_leftMulMatrix b, hgen, AdjoinRoot.minpoly_root hf0, hmon.leadingCoeff]
    simp
  have hnorm : Algebra.norm ℚ (algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f)
      = (Algebra.leftMulMatrix b.basis (algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f)).det :=
    Algebra.norm_eq_matrix_det b.basis _
  refine hnorm.trans ?_
  have hscalar : Algebra.leftMulMatrix b.basis (algebraMap ℚ (AdjoinRoot f) x) = Matrix.scalar _ x := by
    exact (AlgHom.commutes (Algebra.leftMulMatrix b.basis) x).trans rfl
  rw [map_sub, hscalar, ← hgen, ← Matrix.eval_charpoly, hchar, hf]
  simp [hxy]

end MPP.Solutions.Bsd074
