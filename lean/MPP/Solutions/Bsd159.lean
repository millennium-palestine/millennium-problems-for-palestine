import Mathlib

namespace MPP.Solutions.Bsd159

theorem main : ∀ (p : ℕ) [Fact p.Prime] (m ℓ D : ℕ) (xs : Fin m → ZMod p), m * ℓ < D →
    ∃ g : Polynomial (ZMod p), g ≠ 0 ∧ g.natDegree < D ∧
      ∀ i : Fin m, ∀ k : ℕ, k < ℓ → (Polynomial.hasseDeriv k g).eval (xs i) = 0 := by
  intro p _ m ℓ D xs hD
  -- the evaluation map of the first D coefficients, one coordinate per (point, derivative order)
  let L : Polynomial.degreeLT (ZMod p) D →ₗ[ZMod p] (Fin m × Fin ℓ → ZMod p) :=
    LinearMap.pi fun ik => ((Polynomial.leval (xs ik.1)) ∘ₗ (Polynomial.hasseDeriv ik.2)) ∘ₗ
      (Polynomial.degreeLT (ZMod p) D).subtype
  have hfin : Module.finrank (ZMod p) (Polynomial.degreeLT (ZMod p) D) = D := by
    rw [(Polynomial.degreeLTEquiv (ZMod p) D).finrank_eq, Module.finrank_fin_fun]
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [hfin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    exact hD
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hne : (v : Polynomial (ZMod p)) ≠ 0 := fun h => hv0 (Subtype.ext h)
  refine ⟨(v : Polynomial (ZMod p)), hne, ?_, ?_⟩
  · have hdeg := v.2
    rw [Polynomial.mem_degreeLT] at hdeg
    exact (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hdeg
  · intro i k hk
    have hLi := congrFun (LinearMap.mem_ker.mp hv) (i, ⟨k, hk⟩)
    simpa [L] using hLi

end MPP.Solutions.Bsd159
