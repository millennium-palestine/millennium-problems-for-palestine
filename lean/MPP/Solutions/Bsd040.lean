import Mathlib

namespace MPP.Solutions.Bsd040

theorem main : ∀ S : Finset ℕ, Set.Finite {d : ℤ | Squarefree d.natAbs ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p ∈ S} := by
  intro S
  set T : Finset ℕ := S.filter Nat.Prime with hT
  set N : ℕ := ∏ p ∈ T, p with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Finset.prod_ne_zero_iff]
    intro p hp
    exact (Finset.mem_filter.mp hp).2.ne_zero
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  rintro d ⟨hsq, hS⟩
  have hsub : d.natAbs.primeFactors ⊆ T := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d.natAbs := Nat.dvd_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨hS p hpp (Int.ofNat_dvd_left.mpr hpd), hpp⟩
  have hdvd : d.natAbs ∣ N := by
    have h := Finset.prod_dvd_prod_of_subset d.natAbs.primeFactors T (fun p => p) hsub
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at h
  have hle : d.natAbs ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
  have habs : |d| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hle
  exact abs_le.mp habs

end MPP.Solutions.Bsd040
