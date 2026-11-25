import Mathlib

namespace MPP.Solutions.Bsd189

theorem aux187 : ∀ σ : ℝ, 3 / 2 < σ →
    Summable (fun p : ℕ => if p.Prime then (p : ℝ) ^ (1 / 2 - σ) else 0) := by
  intro σ hσ
  have hexp : 1 / 2 - σ < -1 := by linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (Real.summable_nat_rpow.mpr hexp)
  · split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact le_refl _
  · split_ifs with h
    · exact le_refl _
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _


theorem aux186 : ∀ (p : ℕ) (A σ : ℝ) (u : ℕ → ℝ), p.Prime → 0 ≤ A → A * (p : ℝ) ^ (1 / 2 - σ) ≤ 1 / 2 →
    (∀ k : ℕ, |u k| ≤ ((k : ℝ) + 1) * A ^ k * (p : ℝ) ^ ((k : ℝ) / 2)) →
    Summable (fun k : ℕ => |u k| / (p : ℝ) ^ (σ * k)) ∧
      ∑' k : ℕ, |u k| / (p : ℝ) ^ (σ * k) ≤ 1 + 8 * (A * (p : ℝ) ^ (1 / 2 - σ)) := by
  intro p A σ u hp hA hx hu
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx0 : 0 ≤ A * (p : ℝ) ^ (1 / 2 - σ) := mul_nonneg hA (Real.rpow_nonneg hp0.le _)
  set x : ℝ := A * (p : ℝ) ^ (1 / 2 - σ) with hxdef
  have hx1 : x < 1 := by linarith
  have hterm : ∀ k : ℕ, |u k| / (p : ℝ) ^ (σ * k) ≤ ((k : ℝ) + 1) * x ^ k := by
    intro k
    have hpk : 0 < (p : ℝ) ^ (σ * k) := Real.rpow_pos_of_pos hp0 _
    have hkey : (p : ℝ) ^ ((k : ℝ) / 2) / (p : ℝ) ^ (σ * k) = ((p : ℝ) ^ (1 / 2 - σ)) ^ k := by
      rw [← Real.rpow_sub hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1
      ring
    calc |u k| / (p : ℝ) ^ (σ * k)
        ≤ (((k : ℝ) + 1) * A ^ k * (p : ℝ) ^ ((k : ℝ) / 2)) / (p : ℝ) ^ (σ * k) :=
          div_le_div_of_nonneg_right (hu k) hpk.le
      _ = ((k : ℝ) + 1) * A ^ k * ((p : ℝ) ^ ((k : ℝ) / 2) / (p : ℝ) ^ (σ * k)) := by ring
      _ = ((k : ℝ) + 1) * A ^ k * ((p : ℝ) ^ (1 / 2 - σ)) ^ k := by rw [hkey]
      _ = ((k : ℝ) + 1) * x ^ k := by rw [hxdef, mul_pow]; ring
  have hgeo : HasSum (fun k : ℕ => ((k : ℝ) + 1) * x ^ k) (1 / (1 - x) ^ 2) := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
    have h2 := hasSum_geometric_of_lt_one hx0 hx1
    have h3 := h1.add h2
    have hne : (1 - x) ≠ 0 := by linarith
    have heq : x / (1 - x) ^ 2 + (1 - x)⁻¹ = 1 / (1 - x) ^ 2 := by
      field_simp
      ring
    rw [heq] at h3
    have hfun : (fun k : ℕ => ((k : ℝ) + 1) * x ^ k) = (fun b : ℕ => (b : ℝ) * x ^ b + x ^ b) := by
      funext k
      ring
    rw [hfun]
    exact h3
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) * x ^ k) := hgeo.summable
  have hnn : ∀ k : ℕ, 0 ≤ |u k| / (p : ℝ) ^ (σ * k) := fun k =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg hp0.le _)
  have hs : Summable (fun k : ℕ => |u k| / (p : ℝ) ^ (σ * k)) :=
    Summable.of_nonneg_of_le hnn hterm hsum
  refine ⟨hs, ?_⟩
  have hg : 0 ≤ 6 - 15 * x + 8 * x ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - x) (by linarith : (0 : ℝ) ≤ 11 - 8 * x)]
  have hfin : 1 / (1 - x) ^ 2 ≤ 1 + 8 * x := by
    have hpos : 0 < (1 - x) ^ 2 := by nlinarith
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx0 hg]
  calc ∑' k : ℕ, |u k| / (p : ℝ) ^ (σ * k) ≤ ∑' k : ℕ, ((k : ℝ) + 1) * x ^ k :=
        Summable.tsum_le_tsum hterm hs hsum
    _ = 1 / (1 - x) ^ 2 := hgeo.tsum_eq
    _ ≤ 1 + 8 * x := hfin


theorem aux188 : ∀ (f : ℕ → ℝ) (σ : ℝ) (N : ℕ),
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

theorem main : ∀ (f : ℕ → ℝ) (σ A : ℝ) (S : Finset ℕ), 3 / 2 < σ → 0 ≤ A →
    (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n) →
    (∀ p : ℕ, p.Prime → ∀ k : ℕ, |f (p ^ k)| ≤ ((k : ℝ) + 1) * A ^ k * (p : ℝ) ^ ((k : ℝ) / 2)) →
    (∀ p : ℕ, p.Prime → p ∉ S → A * (p : ℝ) ^ (1 / 2 - σ) ≤ 1 / 2) →
    (∀ p ∈ S, Summable (fun k : ℕ => |f (p ^ k)| / (p : ℝ) ^ (σ * k))) →
    Summable (fun n : ℕ => |f n| / (n : ℝ) ^ σ) := by
  intro f σ A S hσ hA hmult hpp hsmall hSsum
  have hσpos : (0 : ℝ) < σ := by linarith
  have hterm_nn : ∀ p k : ℕ, 0 ≤ |f (p ^ k)| / (p : ℝ) ^ (σ * k) := fun p k =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  set T : ℕ → ℝ := fun p => ∑' k : ℕ, |f (p ^ k)| / (p : ℝ) ^ (σ * k) with hTdef
  have hTnn : ∀ p, 0 ≤ T p := fun p => tsum_nonneg (fun k => hterm_nn p k)
  set x : ℕ → ℝ := fun p => A * (p : ℝ) ^ (1 / 2 - σ) with hxdef
  have hxnn : ∀ p, 0 ≤ x p := fun p => mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  -- G p bounds the local partial sums at p
  set G : ℕ → ℝ := fun p => if p ∈ S then T p else 1 + 8 * x p with hGdef
  have hloc : ∀ p, p.Prime → ∀ N : ℕ,
      ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) ≤ G p := by
    intro p hp N
    by_cases hpS : p ∈ S
    · have hsum : Summable (fun k : ℕ => |f (p ^ k)| / (p : ℝ) ^ (σ * k)) := hSsum p hpS
      have hle : ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) ≤
          ∑' k : ℕ, |f (p ^ k)| / (p : ℝ) ^ (σ * k) :=
        Summable.sum_le_tsum _ (fun k _ => hterm_nn p k) hsum
      simp only [hGdef, if_pos hpS]
      exact hle
    · obtain ⟨hs, hle⟩ := aux186 p A σ (fun k => f (p ^ k)) hp hA (hsmall p hp hpS)
        (fun k => hpp p hp k)
      have hpart : ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) ≤
          ∑' k : ℕ, |f (p ^ k)| / (p : ℝ) ^ (σ * k) :=
        Summable.sum_le_tsum _ (fun k _ => hterm_nn p k) hs
      simp only [hGdef, if_neg hpS]
      exact hpart.trans hle
  -- the prime majorant y
  set y : ℕ → ℝ := fun p => if p.Prime then x p else 0 with hydef
  have hy_nn : ∀ p, 0 ≤ y p := by
    intro p
    by_cases hp : p.Prime
    · simp only [hydef, if_pos hp]; exact hxnn p
    · simp only [hydef, if_neg hp]; exact le_refl 0
  have hy_sum : Summable y := by
    refine ((aux187 σ hσ).mul_left A).congr (fun p => ?_)
    by_cases hp : p.Prime
    · simp only [hydef, hxdef, if_pos hp]
    · simp only [hydef, if_neg hp, mul_zero]
  -- the factors G p and their exponential majorant
  set T' : ℕ → ℝ := fun p => if p ∈ S then T p else 0 with hT'def
  have hT'nn : ∀ p, 0 ≤ T' p := by
    intro p
    by_cases hpS : p ∈ S
    · simp only [hT'def, if_pos hpS]; exact hTnn p
    · simp only [hT'def, if_neg hpS]; exact le_refl 0
  have hGexp : ∀ p, p.Prime → G p ≤ Real.exp (T' p + 8 * y p) := by
    intro p hp
    have hyp : y p = x p := by simp only [hydef, if_pos hp]
    by_cases hpS : p ∈ S
    · have h1 : T p ≤ Real.exp (T p) := by linarith [Real.add_one_le_exp (T p)]
      have h2 : Real.exp (T p) ≤ Real.exp (T' p + 8 * y p) := by
        apply Real.exp_le_exp.mpr
        have : T' p = T p := by simp only [hT'def, if_pos hpS]
        rw [this]
        linarith [hy_nn p]
      simp only [hGdef, if_pos hpS]
      exact h1.trans h2
    · have h1 : 1 + 8 * x p ≤ Real.exp (8 * x p) := by linarith [Real.add_one_le_exp (8 * x p)]
      have h2 : Real.exp (8 * x p) = Real.exp (T' p + 8 * y p) := by
        congr 1
        simp only [hT'def, if_neg hpS, hyp, zero_add]
      simp only [hGdef, if_neg hpS]
      rw [← h2]
      exact h1
  -- the partial products over the primes
  have hprod : ∀ N : ℕ,
      ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) ≤
      Real.exp (∑ p ∈ S, T p + 8 * ∑' p, y p) := by
    intro N
    set P := (Finset.range (N + 1)).filter Nat.Prime with hPdef
    have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
    have hsum_nn : ∀ p, 0 ≤ ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) :=
      fun p => Finset.sum_nonneg (fun k _ => hterm_nn p k)
    calc ∏ p ∈ P, ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k)
        ≤ ∏ p ∈ P, Real.exp (T' p + 8 * y p) :=
          Finset.prod_le_prod (fun p _ => hsum_nn p)
            (fun p hp => (hloc p (hPprime p hp) N).trans (hGexp p (hPprime p hp)))
      _ = Real.exp (∑ p ∈ P, (T' p + 8 * y p)) := by rw [Real.exp_sum]
      _ ≤ Real.exp (∑ p ∈ S, T p + 8 * ∑' p, y p) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          have h1 : ∑ p ∈ P, T' p ≤ ∑ p ∈ S, T p := by
            calc ∑ p ∈ P, T' p ≤ ∑ p ∈ P ∪ S, T' p :=
                  Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
                    (fun p _ _ => hT'nn p)
              _ = ∑ p ∈ S, T' p :=
                  (Finset.sum_subset Finset.subset_union_right (fun p _ hpS => by
                    simp only [hT'def, if_neg hpS])).symm
              _ = ∑ p ∈ S, T p :=
                  Finset.sum_congr rfl (fun p hp => by simp only [hT'def, if_pos hp])
          have h2 : ∑ p ∈ P, y p ≤ ∑' p, y p :=
            Summable.sum_le_tsum _ (fun p _ => hy_nn p) hy_sum
          linarith
  -- the partial sums of the target series
  set g : ℕ → ℝ := fun n => |f n| / (n : ℝ) ^ σ with hgdef
  have hg_nn : ∀ n, 0 ≤ g n := fun n =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hg0 : g 0 = 0 := by
    simp only [hgdef, Nat.cast_zero, Real.zero_rpow hσpos.ne', div_zero]
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), g n ≤ Real.exp (∑ p ∈ S, T p + 8 * ∑' p, y p) := by
    intro N
    have hsub : Finset.range (N + 1) ⊆ insert 0 (Finset.Icc 1 N) := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Icc.mpr
          ⟨h, by have := Finset.mem_range.mp hn; omega⟩))
    calc ∑ n ∈ Finset.range (N + 1), g n
        ≤ ∑ n ∈ insert 0 (Finset.Icc 1 N), g n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg_nn n)
      _ = ∑ n ∈ Finset.Icc 1 N, g n := by
          rw [Finset.sum_insert (by simp), hg0, zero_add]
      _ ≤ ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            ∑ k ∈ Finset.range (N + 1), |f (p ^ k)| / (p : ℝ) ^ (σ * k) :=
          aux188 f σ N hmult
      _ ≤ Real.exp (∑ p ∈ S, T p + 8 * ∑' p, y p) := hprod N
  refine summable_of_sum_range_le (c := Real.exp (∑ p ∈ S, T p + 8 * ∑' p, y p)) (fun n => hg_nn n) (fun n => ?_)
  cases n with
  | zero => rw [Finset.sum_range_zero]; exact (Real.exp_pos _).le
  | succ N => exact hpart N

end MPP.Solutions.Bsd189
