import Mathlib

namespace MPP.Solutions.Bsd083

open Polynomial

theorem main : ∀ (p q x : ℚ) (f : Polynomial ℚ), f = X ^ 3 + C p * X + C q →
    ∀ β : AdjoinRoot f, β ^ 2 = algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f →
      ∃ u v w : ℚ, u ^ 2 - 2 * q * v * w = x ∧ 2 * u * v - 2 * p * v * w - q * w ^ 2 = -1 ∧
        v ^ 2 + 2 * u * w - p * w ^ 2 = 0 := by
  intro p q x f hf β hβ
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hdegf : f.degree = 3 := by
    rw [hf]
    compute_degree!
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective β
  -- reduce g modulo f: the remainder has degree < 3, so it is u + vX + wX²
  have hrdeg : (g %ₘ f).degree < 3 := by
    rw [← hdegf]
    exact Polynomial.degree_modByMonic_lt g hmon
  obtain ⟨u, v, w, hr_eq⟩ : ∃ u v w : ℚ, g %ₘ f = C u + C v * X + C w * X ^ 2 := by
    refine ⟨(g %ₘ f).coeff 0, (g %ₘ f).coeff 1, (g %ₘ f).coeff 2, ?_⟩
    ext n
    rcases n with _ | _ | _ | n
    · simp
    · simp
    · simp
    · have h0 := (Polynomial.degree_lt_iff_coeff_zero (g %ₘ f) 3).mp hrdeg (n + 3) (by omega)
      simp [h0]
  have hβ' : AdjoinRoot.mk f g = AdjoinRoot.mk f (C u + C v * X + C w * X ^ 2) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨g /ₘ f, by linear_combination hr_eq - (Polynomial.modByMonic_add_div g f)⟩
  rw [hβ'] at hβ
  -- f divides (u + vX + wX²)² - x + X
  have hP : AdjoinRoot.mk f ((C u + C v * X + C w * X ^ 2) ^ 2 - C x + X) = 0 := by
    simp only [map_add, map_sub, map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.algebraMap_eq] at hβ ⊢
    linear_combination hβ
  obtain ⟨k, hk⟩ := AdjoinRoot.mk_eq_zero.mp hP
  -- explicit division: P = f · (w²X + 2vw) + (a0 + a1 X + a2 X²)
  have hident : (C u + C v * X + C w * X ^ 2) ^ 2 - C x + X =
      f * (C (w ^ 2) * X + C (2 * v * w)) +
        (C (u ^ 2 - x - 2 * q * v * w) + C (2 * u * v + 1 - 2 * p * v * w - q * w ^ 2) * X +
          C (v ^ 2 + 2 * u * w - p * w ^ 2) * X ^ 2) := by
    rw [hf]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
    ring
  -- name the three remainder coefficients, so that simp does not expand the C-terms
  obtain ⟨a0, ha0⟩ : ∃ a : ℚ, a = u ^ 2 - x - 2 * q * v * w := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a : ℚ, a = 2 * u * v + 1 - 2 * p * v * w - q * w ^ 2 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : ℚ, a = v ^ 2 + 2 * u * w - p * w ^ 2 := ⟨_, rfl⟩
  rw [← ha0, ← ha1, ← ha2] at hident
  have hdvd : f ∣ C a0 + C a1 * X + C a2 * X ^ 2 := by
    refine ⟨k - (C (w ^ 2) * X + C (2 * v * w)), ?_⟩
    linear_combination hk - hident
  have hlt : (C a0 + C a1 * X + C a2 * X ^ 2).degree < f.degree := by
    rw [hdegf]
    have hle : (C a0 + C a1 * X + C a2 * X ^ 2).natDegree ≤ 2 := by
      compute_degree!
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hle) (by norm_num)
  have hzero := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hlt
  have e0 := congrArg (fun t => Polynomial.coeff t 0) hzero
  have e1 := congrArg (fun t => Polynomial.coeff t 1) hzero
  have e2 := congrArg (fun t => Polynomial.coeff t 2) hzero
  simp [Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow] at e0 e1 e2
  refine ⟨u, v, w, ?_, ?_, ?_⟩
  · linear_combination e0 - ha0
  · linear_combination e1 - ha1
  · linear_combination e2 - ha2

end MPP.Solutions.Bsd083
