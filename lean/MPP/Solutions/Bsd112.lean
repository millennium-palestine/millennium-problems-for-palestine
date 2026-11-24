import Mathlib

namespace MPP.Solutions.Bsd112

theorem main : ∀ (p e : ℚ) (g : Polynomial ℚ), g = Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) →
    Irreducible g → ∀ (x : ℚ) (β : AdjoinRoot g), β ^ 2 = algebraMap ℚ (AdjoinRoot g) x - AdjoinRoot.root g →
      ∃ u v : ℚ, u ^ 2 - v ^ 2 * (e ^ 2 + p) = x ∧ 2 * u * v - e * v ^ 2 = -1 := by
  intro p e g hg hirr x β hβ
  have hmonic : g.Monic := by
    rw [hg]
    monicity!
  have hdeg : g.degree = 2 := by
    rw [hg]
    compute_degree!
  haveI : Nontrivial (AdjoinRoot g) := AdjoinRoot.nontrivial g (by rw [hdeg]; decide)
  -- θ is a root of g
  have hθ : AdjoinRoot.root g ^ 2 + algebraMap ℚ (AdjoinRoot g) e * AdjoinRoot.root g +
      algebraMap ℚ (AdjoinRoot g) (e ^ 2 + p) = 0 := by
    have h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p)) = 0 := by
      rw [← hg]
      exact AdjoinRoot.mk_self
    have h1 := h0
    simp only [map_add, map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq] at h1 ⊢
    exact h1
  -- θ is not rational
  have hθne : ∀ a : ℚ, algebraMap ℚ (AdjoinRoot g) a ≠ AdjoinRoot.root g := by
    intro a ha
    have hg0 : Polynomial.aeval (AdjoinRoot.root g) g = 0 := by
      rw [Polynomial.aeval_def]
      exact AdjoinRoot.eval₂_root g
    rw [← ha, Polynomial.aeval_algebraMap_apply] at hg0
    have hga : g.eval a = 0 := (map_eq_zero_iff (algebraMap ℚ (AdjoinRoot g)) (algebraMap ℚ (AdjoinRoot g)).injective).mp hg0
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := a) hga
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  -- a + bθ = 0 forces a = b = 0 (no field structure on L is needed)
  have indep : ∀ a b : ℚ, algebraMap ℚ (AdjoinRoot g) a + algebraMap ℚ (AdjoinRoot g) b * AdjoinRoot.root g = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have hb0 : b = 0 := by
      by_contra hb
      apply hθne (-a / b)
      have e1 : algebraMap ℚ (AdjoinRoot g) (1 / b) * algebraMap ℚ (AdjoinRoot g) b = 1 := by
        rw [← map_mul, one_div_mul_cancel hb, map_one]
      have e2 : algebraMap ℚ (AdjoinRoot g) (-a / b) =
          algebraMap ℚ (AdjoinRoot g) (1 / b) * (-algebraMap ℚ (AdjoinRoot g) a) := by
        rw [← map_neg, ← map_mul]
        congr 1
        ring
      rw [e2]
      linear_combination (-(algebraMap ℚ (AdjoinRoot g) (1 / b))) * hab + AdjoinRoot.root g * e1
    subst hb0
    refine ⟨?_, rfl⟩
    rw [map_zero, zero_mul, add_zero] at hab
    exact (map_eq_zero_iff _ (algebraMap ℚ (AdjoinRoot g)).injective).mp hab
  -- every element of L is c₀ + c₁ θ
  obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective β
  have hsplit : AdjoinRoot.mk g h = AdjoinRoot.mk g (h %ₘ g) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div h g]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  have hr1 : (h %ₘ g).degree ≤ 1 := by
    have h2 := Polynomial.degree_modByMonic_lt h hmonic
    rw [hdeg] at h2
    exact Order.le_of_lt_succ h2
  obtain ⟨u, v, huv⟩ : ∃ u v : ℚ, h %ₘ g = Polynomial.C v * Polynomial.X + Polynomial.C u :=
    ⟨_, _, Polynomial.eq_X_add_C_of_degree_le_one hr1⟩
  have hβ' : AdjoinRoot.mk g h = algebraMap ℚ (AdjoinRoot g) u + algebraMap ℚ (AdjoinRoot g) v * AdjoinRoot.root g := by
    rw [hsplit, huv]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
    ring
  rw [hβ'] at hβ
  -- the coefficient relation: (u² − v²(e²+p) − x) + (2uv − ev² + 1)θ = 0
  have key : algebraMap ℚ (AdjoinRoot g) (u ^ 2 - v ^ 2 * (e ^ 2 + p) - x) +
      algebraMap ℚ (AdjoinRoot g) (2 * u * v - e * v ^ 2 + 1) * AdjoinRoot.root g = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat] at hθ hβ ⊢
    linear_combination hβ - (algebraMap ℚ (AdjoinRoot g) v) ^ 2 * hθ
  obtain ⟨ha0, hb0⟩ := indep _ _ key
  exact ⟨u, v, by linarith, by linarith⟩

end MPP.Solutions.Bsd112
