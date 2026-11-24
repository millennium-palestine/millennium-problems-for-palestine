import Mathlib

namespace MPP.Solutions.Bsd095

theorem main : ∀ (ι : Type) (f : ι → ArithmeticFunction ℤ) (i₀ : ι) (p k : ℕ), p.Prime →
    (∀ i, i ≠ i₀ → ∀ j, j ≤ k → f i (p ^ j) = (1 : ArithmeticFunction ℤ) (p ^ j)) →
    (∀ n : ℕ, ∀ᶠ i in Filter.cofinite, f i n = (1 : ArithmeticFunction ℤ) n) →
    ArithmeticFunction.eulerProduct f (p ^ k) = f i₀ (p ^ k) := by
  intro ι f i₀ p k hp hloc hcof
  classical
  -- every other factor is the identity at all divisors of p ^ k
  have key : ∀ t : Finset ι, i₀ ∉ t → ∀ y : ℕ, y ∣ p ^ k →
      (∏ i ∈ t, f i) y = (1 : ArithmeticFunction ℤ) y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ y _
      simp
    | @insert a t ha ih =>
      intro hi y hy
      have hai : a ≠ i₀ := fun h => hi (h ▸ Finset.mem_insert_self a t)
      have hit : i₀ ∉ t := fun h => hi (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert ha, ArithmeticFunction.mul_apply]
      calc ∑ x ∈ y.divisorsAntidiagonal, f a x.1 * (∏ i ∈ t, f i) x.2
          = ∑ x ∈ y.divisorsAntidiagonal, (1 : ArithmeticFunction ℤ) x.1 * (1 : ArithmeticFunction ℤ) x.2 := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have h1 : x.1 ∣ p ^ k :=
              (Nat.mem_divisors.mp (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1.trans hy
            have h2 : x.2 ∣ p ^ k :=
              (Nat.mem_divisors.mp (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1.trans hy
            obtain ⟨m, hm, hxm⟩ := (Nat.dvd_prime_pow hp).mp h1
            rw [hxm, hloc a hai m hm, ih hit x.2 h2]
        _ = ((1 : ArithmeticFunction ℤ) * (1 : ArithmeticFunction ℤ)) y :=
            (ArithmeticFunction.mul_apply).symm
        _ = (1 : ArithmeticFunction ℤ) y := by rw [mul_one]
  -- the partial products containing i₀ have the value f i₀ at p ^ k
  have partial_val : ∀ s : Finset ι, i₀ ∈ s → (∏ i ∈ s, f i) (p ^ k) = f i₀ (p ^ k) := by
    intro s hs
    rw [← Finset.insert_erase hs, Finset.prod_insert (Finset.notMem_erase i₀ s)]
    calc (f i₀ * ∏ i ∈ s.erase i₀, f i) (p ^ k)
        = (f i₀ * (1 : ArithmeticFunction ℤ)) (p ^ k) := by
          rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
          refine Finset.sum_congr rfl fun x hx => ?_
          have h2 : x.2 ∣ p ^ k :=
            (Nat.mem_divisors.mp (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
          rw [key (s.erase i₀) (Finset.notMem_erase i₀ s) x.2 h2]
      _ = f i₀ (p ^ k) := by rw [mul_one]
  -- read the Euler product off the eventual value of the partial products
  have hconv := ArithmeticFunction.tendsTo_eulerProduct_of_tendsTo f hcof (p ^ k)
  have hev : ∀ᶠ s : Finset ι in Filter.atTop, i₀ ∈ s :=
    (Filter.eventually_ge_atTop ({i₀} : Finset ι)).mono fun s hs =>
      Finset.singleton_subset_iff.mp hs
  obtain ⟨s, hs1, hs2⟩ := ((hconv).and hev).exists
  rw [← hs1]
  exact partial_val s hs2

end MPP.Solutions.Bsd095
