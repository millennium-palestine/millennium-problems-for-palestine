import Mathlib

namespace MPP.Solutions.Bsd174

theorem euler_trich (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (y : ZMod p) :
    (y = 0 ∧ quadraticChar (ZMod p) y = 0) ∨
    (y ≠ 0 ∧ y ^ ((p - 1) / 2) = 1 ∧ quadraticChar (ZMod p) y = 1) ∨
    (y ≠ 0 ∧ y ^ ((p - 1) / 2) = -1 ∧ quadraticChar (ZMod p) y = -1) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hhalf : (p - 1) / 2 = p / 2 := by omega
  rw [hhalf]
  by_cases hy : y = 0
  · left
    exact ⟨hy, by simp [hy]⟩
  · right
    by_cases hs : IsSquare y
    · left
      refine ⟨hy, (ZMod.euler_criterion (p := p) hy).mp hs, ?_⟩
      exact (quadraticChar_one_iff_isSquare hy).mpr hs
    · right
      refine ⟨hy, ?_, quadraticChar_neg_one_iff_not_isSquare.mpr hs⟩
      rcases ZMod.pow_div_two_eq_neg_one_or_one (p := p) hy with h | h
      · exact absurd ((ZMod.euler_criterion (p := p) hy).mpr h) hs
      · exact h

theorem one_ne_neg_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (1 : ZMod p) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)

theorem char_eq_indicators (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (y : ZMod p) :
    (quadraticChar (ZMod p) y : ℝ) =
      (if y ^ ((p - 1) / 2) = 1 then 1 else 0) - (if y ^ ((p - 1) / 2) = -1 then 1 else 0) := by
  have h12 := one_ne_neg_one p hp2
  have h12' : (-1 : ZMod p) ≠ 1 := fun h => h12 h.symm
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have he : (p - 1) / 2 ≠ 0 := by
    have := hp.out.two_le
    omega
  rcases euler_trich p hp2 y with ⟨hy, hχ⟩ | ⟨hy, h1, hχ⟩ | ⟨hy, h1, hχ⟩
  · simp [hy, zero_pow he]
  · rw [hχ, h1]
    simp [h12]
  · rw [hχ, h1]
    simp [h12']

theorem main : (∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b : ZMod p,
      4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → ∀ ε : ZMod p, (ε = 1 ∨ ε = -1) →
      2 * ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = ε)).card : ℝ)
        - (p : ℝ) ≤ C * Real.sqrt (p : ℝ)) →
    ∃ C' : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b : ZMod p,
      4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
      |∑ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 + a * x + b) : ℝ)| ≤ C' * Real.sqrt (p : ℝ) := by
  rintro ⟨C, hC⟩
  refine ⟨|C| + 3, ?_⟩
  intro p hp hp2 a b hab
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have he : (p - 1) / 2 ≠ 0 := by
    have := hp.out.two_le
    omega
  have h12 := one_ne_neg_one p hp2
  have h12' : (-1 : ZMod p) ≠ 1 := fun h => h12 h.symm
  -- the three level sets partition ZMod p: N₊ + N₋ + z = p
  have hpart : (Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = 1)).card
      + (Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = -1)).card
      + (Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card = p := by
    calc _ = ∑ x : ZMod p, ((if (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = 1 then 1 else 0)
            + (if (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = -1 then 1 else 0)
            + (if x ^ 3 + a * x + b = 0 then 1 else 0) : ℕ) := by
          simp [Finset.sum_add_distrib, Finset.sum_boole]
      _ = ∑ _x : ZMod p, 1 := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          by_cases h0 : x ^ 3 + a * x + b = 0
          · simp [h0, zero_pow he]
          · rcases euler_trich p hp2 (x ^ 3 + a * x + b) with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, _⟩
            · exact absurd h1 h0
            · simp [h2, h12, h0]
            · simp [h2, h12', h0]
      _ = p := by simp
  -- the bounds on the level sets and on the number of roots
  have hplus := hC p hp2 a b hab 1 (Or.inl rfl)
  have hminus := hC p hp2 a b hab (-1) (Or.inr rfl)
  have hz : (Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card ≤ 3 := by
    let P : Polynomial (ZMod p) := Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b
    have hP0 : P ≠ 0 := by
      intro h
      have := congrArg (fun q => Polynomial.coeff q 3) h
      simp [P] at this
    have hdeg : P.natDegree ≤ 3 := by
      simp only [P]
      compute_degree!
    have hsub : (Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).val ⊆ P.roots := by
      intro x hx
      rw [Finset.mem_val, Finset.mem_filter] at hx
      rw [Polynomial.mem_roots hP0]
      simp [P, Polynomial.IsRoot, hx.2]
    exact (Polynomial.card_le_degree_of_subset_roots hsub).trans hdeg
  have hS : (∑ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 + a * x + b) : ℝ)) =
      ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = 1)).card : ℝ)
        - ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = -1)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun x _ => char_eq_indicators p hp2 (x ^ 3 + a * x + b))]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_boole]
  have hpart' : ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = 1)).card : ℝ)
      + ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = -1)).card : ℝ)
      + ((Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card : ℝ) = (p : ℝ) := by
    exact_mod_cast hpart
  have hz' : ((Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card : ℝ) ≤ 3 := by
    exact_mod_cast hz
  have h1 : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hp.out.one_lt.le)
  have hC1 : C * Real.sqrt (p : ℝ) ≤ |C| * Real.sqrt (p : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
  have hexp : (|C| + 3) * Real.sqrt (p : ℝ) = |C| * Real.sqrt (p : ℝ) + 3 * Real.sqrt (p : ℝ) := by ring
  rw [hS, abs_le]
  constructor
  · linarith
  · linarith

end MPP.Solutions.Bsd174
