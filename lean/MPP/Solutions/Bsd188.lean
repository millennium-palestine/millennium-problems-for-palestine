import Mathlib

namespace MPP.Solutions.Bsd188

theorem main : ∀ (f : ℕ → ℝ) (σ : ℝ) (N : ℕ),
    (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n) →
    ∑ n ∈ Finset.Icc 1 N, |f n| / (n : ℝ) ^ σ ≤
      ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) := by
  classical
  intro f σ N hf
  set P := (Finset.range (N + 1)).filter Nat.Prime with hPdef
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  rcases eq_or_ne (f 1) 0 with h1 | h1
  · -- f vanishes on every positive integer
    have hzero : ∀ n : ℕ, 0 < n → f n = 0 := by
      intro n hn
      have := hf n 1 hn one_pos (Nat.coprime_one_right n)
      rw [mul_one, h1, mul_zero] at this
      exact this
    rw [Finset.sum_eq_zero (fun n hn => by
      rw [hzero n (Finset.mem_Icc.mp hn).1]
      simp)]
    exact Finset.prod_nonneg (fun p _ => Finset.sum_nonneg (fun k _ =>
      div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)))
  have hf1 : f 1 = 1 := by
    have h := hf 1 1 one_pos one_pos (Nat.coprime_one_left 1)
    rw [mul_one] at h
    have : f 1 * (f 1 - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h1
    · linarith
  -- |f| is multiplicative over finite sets of distinct primes
  have hmul : ∀ (v : ℕ → ℕ) (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      |f (∏ p ∈ s, p ^ v p)| = ∏ p ∈ s, |f (p ^ v p)| := by
    intro v s
    induction s using Finset.induction_on with
    | empty => intro _; simp [hf1]
    | insert a s ha ih =>
      intro hs
      have hap : a.Prime := hs a (Finset.mem_insert_self a s)
      have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih hsp]
      have hpos1 : 0 < a ^ v a := pow_pos hap.pos _
      have hposM : 0 < ∏ p ∈ s, p ^ v p :=
        Finset.prod_pos (fun p hp => pow_pos (hsp p hp).pos _)
      have hcop : Nat.Coprime (a ^ v a) (∏ p ∈ s, p ^ v p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        apply Nat.Coprime.pow
        exact (Nat.coprime_primes hap (hsp p hp)).mpr (fun h => ha (h ▸ hp))
      rw [hf _ _ hpos1 hposM hcop, abs_mul]
  -- every n in [1, N] is the product of its prime powers over P
  have hfac : ∀ n : ℕ, 1 ≤ n → n ≤ N → ∏ p ∈ P, p ^ n.factorization p = n := by
    intro n hn1 hnN
    have hn0 : n ≠ 0 := by omega
    have hsub : n.primeFactors ⊆ P := by
      intro p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      have hle : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
    have h1' : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      have h := Nat.prod_factorization_pow_eq_self hn0
      unfold Finsupp.prod at h
      rw [Nat.support_factorization] at h
      exact h
    have hext : ∏ p ∈ n.primeFactors, p ^ n.factorization p = ∏ p ∈ P, p ^ n.factorization p := by
      apply Finset.prod_subset hsub
      intro p _ hnot
      have hz : n.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      rw [hz, pow_zero]
    rw [← hext]
    exact h1'
  -- the exponents of n are at most N
  have hexp : ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ p ∈ P, n.factorization p ∈ Finset.range (N + 1) := by
    intro n hn1 hnN p hp
    have hpp : p.Prime := hPprime p hp
    have hn0 : n ≠ 0 := by omega
    have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hle : p ^ n.factorization p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    have hlt : n.factorization p < p ^ n.factorization p := Nat.lt_pow_self hpp.one_lt
    exact Finset.mem_range.mpr (by omega)
  -- real powers of a finite product of nonnegative reals
  have hprodrpow : ∀ (x : ℕ → ℝ) (s : Finset ℕ), (∀ p ∈ s, 0 ≤ x p) →
      (∏ p ∈ s, x p) ^ σ = ∏ p ∈ s, (x p) ^ σ := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hx
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.mul_rpow (hx a (Finset.mem_insert_self a s))
          (Finset.prod_nonneg fun p hp => hx p (Finset.mem_insert_of_mem hp)),
        ih (fun p hp => hx p (Finset.mem_insert_of_mem hp))]
  have hpow : ∀ (p v : ℕ), ((p : ℝ) ^ v) ^ σ = (p : ℝ) ^ (σ * (v : ℝ)) := by
    intro p v
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm]
  -- the term of n is the product of its local terms
  have hterm : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      |f n| / (n : ℝ) ^ σ =
        ∏ p ∈ P, |f (p ^ n.factorization p)| / (p : ℝ) ^ (σ * (n.factorization p : ℝ)) := by
    intro n hn1 hnN
    have hm : |f (∏ p ∈ P, p ^ n.factorization p)| = ∏ p ∈ P, |f (p ^ n.factorization p)| :=
      hmul (fun p => n.factorization p) P hPprime
    have hcast : (n : ℝ) = ∏ p ∈ P, (p : ℝ) ^ n.factorization p := by
      have h : ((∏ p ∈ P, p ^ n.factorization p : ℕ) : ℝ) = (n : ℝ) := by
        rw [hfac n hn1 hnN]
      push_cast at h
      exact h.symm
    have hnR : (n : ℝ) ^ σ = ∏ p ∈ P, ((p : ℝ) ^ n.factorization p) ^ σ := by
      rw [hcast]
      exact hprodrpow (fun p => (p : ℝ) ^ n.factorization p) P
        (fun p _ => by positivity)
    rw [hfac n hn1 hnN] at hm
    rw [hm, hnR, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [hpow]
  -- the sum over n is a sum over exponent functions, which lies in the sum over P.pi
  set G : ((p : ℕ) → p ∈ P → ℕ) → ℝ := fun φ =>
    ∏ x ∈ P.attach, |f (x.1 ^ φ x.1 x.2)| / (x.1 : ℝ) ^ (σ * (φ x.1 x.2 : ℝ)) with hG
  have hGnn : ∀ φ, 0 ≤ G φ := fun φ =>
    Finset.prod_nonneg (fun x _ => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  set ψ : ℕ → ((p : ℕ) → p ∈ P → ℕ) := fun n p _ => n.factorization p with hψ
  have hsum_eq : ∑ n ∈ Finset.Icc 1 N, |f n| / (n : ℝ) ^ σ = ∑ n ∈ Finset.Icc 1 N, G (ψ n) := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨h1n, hnN⟩ := Finset.mem_Icc.mp hn
    rw [hterm n h1n hnN]
    exact (Finset.prod_attach P (fun p => |f (p ^ n.factorization p)| / (p : ℝ) ^ (σ * (n.factorization p : ℝ)))).symm
  have hinj : Set.InjOn ψ (Finset.Icc 1 N : Set ℕ) := by
    intro x hx y hy hxy
    obtain ⟨hx1, hxN⟩ := Finset.mem_Icc.mp hx
    obtain ⟨hy1, hyN⟩ := Finset.mem_Icc.mp hy
    have hfun : ∀ p, p ∈ P → x.factorization p = y.factorization p :=
      fun p hp => congrFun (congrFun hxy p) hp
    calc x = ∏ p ∈ P, p ^ x.factorization p := (hfac x hx1 hxN).symm
      _ = ∏ p ∈ P, p ^ y.factorization p := Finset.prod_congr rfl (fun p hp => by rw [hfun p hp])
      _ = y := hfac y hy1 hyN
  have himg : ∑ φ ∈ (Finset.Icc 1 N).image ψ, G φ = ∑ n ∈ Finset.Icc 1 N, G (ψ n) :=
    Finset.sum_image (fun x hx y hy hxy => hinj hx hy hxy)
  have hsub : (Finset.Icc 1 N).image ψ ⊆ P.pi (fun _ => Finset.range (N + 1)) := by
    intro φ hφ
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hφ
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_pi.mpr (fun p hp => hexp n hn1 hnN p hp)
  have hprodsum : ∏ p ∈ P, ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * (k : ℝ)) =
      ∑ φ ∈ P.pi (fun _ => Finset.range (N + 1)), G φ :=
    Finset.prod_sum P (fun _ => Finset.range (N + 1))
      (fun p k => |f (p ^ k)| / (p : ℝ) ^ (σ * (k : ℝ)))
  rw [hprodsum, hsum_eq, ← himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun φ _ _ => hGnn φ)

end MPP.Solutions.Bsd188
