import Mathlib

namespace MPP.Solutions.Bsd260

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p) (ρ : MulChar (ZMod p) ℂ), p ≠ 2 → a ≠ 0 →
    (∀ x : ZMod p, ρ x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ)) →
    Complex.normSq (∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ)) = (p : ℝ) := by
  intro p _ a ρ hp2 ha hρ
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  set φ : MulChar (ZMod p) ℂ := ρ ^ 2 with hφdef
  have hφ : ∀ x : ZMod p, φ x = ((quadraticChar (ZMod p) x : ℤ) : ℂ) := by
    intro x
    rw [hφdef, MulChar.pow_apply' ρ (by norm_num : (2 : ℕ) ≠ 0) x]
    exact hρ x
  -- values of ρ on units have modulus one
  have hρ4 : ∀ x : ZMod p, x ≠ 0 → ρ x ^ 4 = 1 := by
    intro x hx
    have h2 : ((quadraticChar (ZMod p) x : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast quadraticChar_sq_one hx
    calc ρ x ^ 4 = (ρ x ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hρ x, h2]
  have hnorm4 : ∀ z : ℂ, z ^ 4 = 1 → Complex.normSq z = 1 := by
    intro z hz
    have h := congrArg Complex.normSq hz
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg z) (by norm_num)).mp h
  have hρnorm : ∀ x : ZMod p, x ≠ 0 → Complex.normSq (ρ x) = 1 :=
    fun x hx => hnorm4 _ (hρ4 x hx)
  have hρconj : ∀ x : ZMod p, starRingEnd ℂ (ρ x) = (ρ x)⁻¹ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, MulChar.map_nonunit ρ not_isUnit_zero]
      simp
    · have hm : ρ x * starRingEnd ℂ (ρ x) = 1 := by
        rw [Complex.mul_conj, hρnorm x hx]
        norm_num
      exact (inv_eq_of_mul_eq_one_right hm).symm
  have hφconj : ∀ y : ZMod p, starRingEnd ℂ (φ y) = (φ y)⁻¹ := by
    intro y
    by_cases hy : y = 0
    · rw [hy, hφ 0, quadraticChar_zero]
      simp
    · rw [hφ y]
      rcases quadraticChar_dichotomy hy with h | h <;> rw [h] <;> norm_num
  -- a nonsquare witnesses the nontriviality hypotheses
  have hchar' : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq_zero]
    exact (Fact.out : p.Prime).pos.ne
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hchar
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn ⟨0, by simp⟩
  have hχn : quadraticChar (ZMod p) n = -1 := by
    rcases quadraticChar_dichotomy hn0 with h | h
    · exact absurd ((quadraticChar_one_iff_isSquare hn0).mp h) hn
    · exact h
  have hnu : IsUnit n := isUnit_iff_ne_zero.mpr hn0
  have hφn : φ n = -1 := by
    rw [hφ n, hχn]
    norm_num
  have hρ1 : ρ ≠ 1 := by
    intro h
    have h1 := hρ n
    rw [h, MulChar.one_apply hnu, hχn] at h1
    norm_num at h1
  have hφ1 : φ ≠ 1 := by
    intro h
    have h1 := hφn
    rw [h, MulChar.one_apply hnu] at h1
    norm_num at h1
  have hρφ : ρ * φ ≠ 1 := by
    intro h
    have h1 : ρ n * φ n = 1 := by
      have := congrArg (fun χ : MulChar (ZMod p) ℂ => χ n) h
      simpa [MulChar.one_apply hnu] using this
    rw [hφn] at h1
    have hρn : ρ n = -1 := by linear_combination -h1
    have h2 := hρ n
    rw [hρn, hχn] at h2
    norm_num at h2
  -- the Jacobi sum and the substitution t = -a s
  have hT : ∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) =
      ρ (-a) * φ a * jacobiSum ρ φ := by
    simp only [← hφ]
    have h1 : ∑ t : ZMod p, ρ t * φ (t + a) =
        ∑ s : ZMod p, ρ (-a * s) * φ (-a * s + a) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ (-a) (neg_ne_zero.mpr ha))
        (fun t => ρ t * φ (t + a))).symm
    rw [h1, jacobiSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [show -a * s + a = a * (1 - s) by ring]
    simp only [map_mul]
    ring
  have hu : Complex.normSq (ρ (-a)) * Complex.normSq (φ a) = 1 := by
    have hφa : Complex.normSq (φ a) = 1 := by
      rw [hφ a]
      rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> norm_num
    rw [hρnorm (-a) (neg_ne_zero.mpr ha), hφa, one_mul]
  have hJ : jacobiSum ρ φ * jacobiSum ρ⁻¹ φ⁻¹ = (Fintype.card (ZMod p) : ℂ) :=
    jacobiSum_mul_jacobiSum_inv hchar' hρ1 hφ1 hρφ
  have hconj : starRingEnd ℂ (jacobiSum ρ φ) = jacobiSum ρ⁻¹ φ⁻¹ := by
    simp only [jacobiSum, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hρconj x, hφconj (1 - x)]
  have hnJ : jacobiSum ρ φ * starRingEnd ℂ (jacobiSum ρ φ) = (p : ℂ) := by
    rw [hconj, hJ, ZMod.card]
  rw [hT, map_mul, map_mul, hu, one_mul]
  rw [Complex.mul_conj] at hnJ
  exact_mod_cast hnJ

end MPP.Solutions.Bsd260
