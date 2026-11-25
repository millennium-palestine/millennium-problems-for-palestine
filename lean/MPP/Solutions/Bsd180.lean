import Mathlib

namespace MPP.Solutions.Bsd180

theorem main : ∀ (K : Type) [Field K] (U m ℓ : ℕ) (B : Fin U → Polynomial K) (xs : Fin m → K),
    LinearIndependent K B → m * ℓ < U →
    ∃ c : Fin U → K, c ≠ 0 ∧ (∑ u, Polynomial.C (c u) * B u) ≠ 0 ∧
      ∀ i : Fin m, ∀ k : ℕ, k < ℓ →
        (Polynomial.hasseDeriv k (∑ u, Polynomial.C (c u) * B u)).eval (xs i) = 0 := by
  intro K _ U m ℓ B xs hB hD
  -- the combination map, and the conditions (point, order) as one linear map
  let Φ : (Fin U → K) →ₗ[K] Polynomial K := Fintype.linearCombination K B
  let L : (Fin U → K) →ₗ[K] (Fin m × Fin ℓ → K) :=
    LinearMap.pi fun ik => ((Polynomial.leval (xs ik.1)) ∘ₗ (Polynomial.hasseDeriv ik.2)) ∘ₗ Φ
  have hfin : Module.finrank K (Fin U → K) = U := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [hfin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    exact hD
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv0, ?_, ?_⟩
  · intro h0
    have hsum : ∑ u, v u • B u = 0 := by
      simpa [Polynomial.smul_eq_C_mul] using h0
    have hall := (Fintype.linearIndependent_iff.mp hB) v hsum
    exact hv0 (funext hall)
  · intro i k hk
    have hLi := congrFun (LinearMap.mem_ker.mp hv) (i, ⟨k, hk⟩)
    simpa [L, Φ, Fintype.linearCombination_apply, Polynomial.smul_eq_C_mul, Polynomial.eval_finset_sum,
      map_sum] using hLi

end MPP.Solutions.Bsd180
