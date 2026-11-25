import Mathlib

namespace MPP.Solutions.Bsd160

theorem main : ∀ (K : Type) [Field K] (g : Polynomial K) (ℓ : ℕ) (S : Finset K), g ≠ 0 →
    (∀ x ∈ S, ∀ k : ℕ, k < ℓ → (Polynomial.hasseDeriv k g).eval x = 0) →
    S.card * ℓ ≤ g.natDegree := by
  intro K _ g ℓ S hg hvan
  -- a root with all Hasse derivatives below ℓ vanishing gives (X - x)^ℓ ∣ g
  have hdvd : ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ ℓ ∣ g := by
    intro x hx
    have h1 : Polynomial.X ^ ℓ ∣ Polynomial.taylor x g := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rw [Polynomial.taylor_coeff]
      exact hvan x hx d hd
    obtain ⟨q, hq⟩ := h1
    have hg' : g = Polynomial.taylor (-x) (Polynomial.taylor x g) := by
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    refine ⟨Polynomial.taylor (-x) q, ?_⟩
    conv_lhs => rw [hg', hq]
    rw [Polynomial.taylor_mul, Polynomial.taylor_X_pow, Polynomial.C_neg, sub_eq_add_neg]
  have hprod : ∏ x ∈ S, (Polynomial.X - Polynomial.C x) ^ ℓ ∣ g := by
    refine Finset.prod_dvd_of_coprime (fun x _ y _ hxy => ?_) hdvd
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hxy).isUnit).pow
  have hdeg := Polynomial.natDegree_le_of_dvd hprod hg
  rw [Polynomial.natDegree_prod _ _ (fun x _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x))] at hdeg
  simpa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul,
    mul_comm] using hdeg

end MPP.Solutions.Bsd160
