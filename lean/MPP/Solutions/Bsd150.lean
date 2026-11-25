import Mathlib

namespace MPP.Solutions.Bsd150

-- helper: bsd-258, proved in its own solution file
theorem lem258 : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 1 →
    ∃ ρ : MulChar (ZMod p) ℂ, ∀ x : ZMod p, ρ x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ) := by
  classical
  intro p _ hp4
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  have h4 : 4 ∣ p - 1 := by omega
  have hp5 : 5 ≤ p := by omega
  -- a generator of the unit group and its order
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  -- discrete logarithm of units
  have hlog : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by
    intro u
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg u))
  choose k hk using hlog
  -- the quadratic character at the generator is −1
  have hgχ : quadraticChar (ZMod p) (g : ZMod p) = -1 := by
    rcases quadraticChar_dichotomy g.ne_zero with h | h
    · exfalso
      have hsq := (quadraticChar_one_iff_isSquare g.ne_zero).mp h
      have hpow := (ZMod.euler_criterion (p := p) g.ne_zero).mp hsq
      have hg1 : g ^ (p / 2) = 1 := by
        ext
        simpa using hpow
      have hdvd := orderOf_dvd_of_pow_eq_one hg1
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · exact h
  have hχpow : ∀ n : ℕ, quadraticChar (ZMod p) ((g : ZMod p) ^ n) =
      (quadraticChar (ZMod p) (g : ZMod p)) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, ih, pow_succ]
  -- the discrete logarithm of a unit, and of a non-unit as 0
  let kz : ZMod p → ℕ := fun x => if h : IsUnit x then k h.unit else 0
  have hkz : ∀ (x : ZMod p) (h : IsUnit x), g ^ kz x = h.unit := by
    intro x h
    simp only [kz, dif_pos h]
    exact hk _
  -- multiplicativity of the exponent modulo 4
  have hmulkey : ∀ x y : ZMod p, IsUnit x → IsUnit y →
      Complex.I ^ kz (x * y) = Complex.I ^ kz x * Complex.I ^ kz y := by
    intro x y hx hy
    have hxy : IsUnit (x * y) := hx.mul hy
    have e1 := hkz _ hxy
    have e2 := hkz x hx
    have e3 := hkz y hy
    have hmul : hxy.unit = hx.unit * hy.unit := by
      ext
      simp
    have hm : g ^ kz (x * y) = g ^ (kz x + kz y) := by
      rw [e1, hmul, ← e2, ← e3, pow_add]
    have hmod : kz (x * y) ≡ kz x + kz y [MOD p - 1] := by
      rw [← hord]
      exact pow_eq_pow_iff_modEq.mp hm
    have hmod4 : kz (x * y) ≡ kz x + kz y [MOD 4] := Nat.ModEq.of_dvd h4 hmod
    unfold Nat.ModEq at hmod4
    rw [← pow_add, pow_eq_pow_mod (kz (x * y)) Complex.I_pow_four,
      pow_eq_pow_mod (kz x + kz y) Complex.I_pow_four, hmod4]
  -- the character itself
  let ρf : ZMod p → ℂ := fun x => if IsUnit x then Complex.I ^ kz x else 0
  have hone : ρf 1 = 1 := by
    have h := hmulkey 1 1 isUnit_one isUnit_one
    rw [mul_one] at h
    have hne : Complex.I ^ kz 1 ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    have h' : Complex.I ^ kz 1 * (Complex.I ^ kz 1 - 1) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hne
    · simp only [ρf, if_pos isUnit_one]
      exact sub_eq_zero.mp h''
  let ρ : MulChar (ZMod p) ℂ :=
    { toFun := ρf
      map_one' := hone
      map_mul' := by
        intro x y
        by_cases hx : IsUnit x <;> by_cases hy : IsUnit y
        · simp only [ρf, if_pos hx, if_pos hy, if_pos (hx.mul hy)]
          exact hmulkey x y hx hy
        · have hxy : ¬IsUnit (x * y) := fun h => hy (isUnit_of_mul_isUnit_right h)
          simp only [ρf, if_pos hx, if_neg hy, if_neg hxy, mul_zero]
        · have hxy : ¬IsUnit (x * y) := fun h => hx (isUnit_of_mul_isUnit_left h)
          simp only [ρf, if_neg hx, if_pos hy, if_neg hxy, zero_mul]
        · have hxy : ¬IsUnit (x * y) := fun h => hx (isUnit_of_mul_isUnit_left h)
          simp only [ρf, if_neg hx, if_neg hy, if_neg hxy, zero_mul]
      map_nonunit' := fun a ha => by simp only [ρf, if_neg ha] }
  refine ⟨ρ, fun x => ?_⟩
  by_cases hx : IsUnit x
  · show ρf x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ)
    have hxg : x = (g : ZMod p) ^ kz x := by
      have h := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) (hkz x hx)
      simp only [Units.val_pow_eq_pow_val] at h
      rw [h, hx.unit_spec]
    have hχx : ((quadraticChar (ZMod p) x : ℤ) : ℂ) = (-1) ^ kz x := by
      conv_lhs => rw [hxg]
      rw [hχpow, hgχ]
      push_cast
      rfl
    rw [hχx]
    simp only [ρf, if_pos hx]
    rw [← pow_mul, mul_comm, pow_mul, Complex.I_sq]
  · have hx0 : x = 0 := by
      simpa using hx
    rw [hx0, MulChar.map_nonunit ρ not_isUnit_zero]
    simp [quadraticChar_zero]

-- helper: bsd-259, proved in its own solution file
theorem lem259 : ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p) (ρ : MulChar (ZMod p) ℂ), p ≠ 2 →
    (∀ x : ZMod p, ρ x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ)) →
    ∑ x : ZMod p, ((quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ) =
      ∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) +
      ∑ t : ZMod p, ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) := by
  intro p _ a ρ hp2 hρ
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  -- the summand is a function of x * x
  have hstep : ∀ x : ZMod p,
      ((quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ) =
        ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) := by
    intro x
    have hx : x ^ 3 + a * x + (0 : ZMod p) = x * (x * x + a) := by ring
    rw [hx, map_mul (quadraticChar (ZMod p)) x (x * x + a), Int.cast_mul, map_mul ρ x x,
      ← hρ x]
    ring
  -- the number of square roots of t
  have hfib : ∀ t : ZMod p,
      ((Finset.univ.filter (fun x : ZMod p => x * x = t)).card : ℂ) =
        ((quadraticChar (ZMod p) t : ℤ) : ℂ) + 1 := by
    intro t
    have h := quadraticChar_card_sqrts hchar t
    simp only [Set.toFinset_setOf] at h
    have h' : Finset.univ.filter (fun x : ZMod p => x * x = t) =
        Finset.univ.filter (fun x : ZMod p => x ^ 2 = t) := by
      ext x
      simp [pow_two]
    rw [h']
    exact_mod_cast h
  calc ∑ x : ZMod p, ((quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ)
      = ∑ x : ZMod p, ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) :=
        Finset.sum_congr rfl (fun x _ => hstep x)
    _ = ∑ t : ZMod p, ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x * x = t),
          ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) :=
        (Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x * x) _).symm
    _ = ∑ t : ZMod p, ((Finset.univ.filter (fun x : ZMod p => x * x = t)).card : ℂ) *
          (ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro t _
        have hin : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x * x = t),
            ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) =
              ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) := by
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t : ZMod p, (ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) +
          ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hfib t, ← hρ t]
        ring
    _ = ∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) +
        ∑ t : ZMod p, ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) :=
        Finset.sum_add_distrib

-- helper: bsd-260, proved in its own solution file
theorem lem260 : ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p) (ρ : MulChar (ZMod p) ℂ), p ≠ 2 → a ≠ 0 →
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

-- helper: bsd-261, proved in its own solution file
theorem lem261 : ∀ (p : ℕ) [Fact p.Prime] (ρ : MulChar (ZMod p) ℂ),
    (∀ x : ZMod p, ρ x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ)) →
    ∀ t : ZMod p, starRingEnd ℂ (ρ t) = ρ t ^ 3 := by
  intro p _ ρ hρ t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [MulChar.map_nonunit ρ not_isUnit_zero]
    simp
  · have h2 : ((quadraticChar (ZMod p) t : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast quadraticChar_sq_one ht
    have h4 : ρ t ^ 4 = 1 := by
      have : ρ t ^ 4 = ((quadraticChar (ZMod p) t : ℤ) : ℂ) ^ 2 := by
        rw [← hρ t]
        ring
      rw [this, h2]
    have hn : Complex.normSq (ρ t) = 1 := by
      have h := congrArg Complex.normSq h4
      rw [map_pow, map_one] at h
      exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) (by norm_num)).mp h
    have hz : ρ t ≠ 0 := by
      intro h
      rw [h] at h4
      norm_num at h4
    have hmul : ρ t * starRingEnd ℂ (ρ t) = 1 := by
      rw [Complex.mul_conj, hn]
      norm_num
    have hc : ρ t * (starRingEnd ℂ (ρ t) - ρ t ^ 3) = 0 := by
      linear_combination hmul - h4
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h hz
    · exact sub_eq_zero.mp h

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p), p ≠ 2 → p % 4 = 1 →
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p))) ^ 2 ≤ 4 * (p : ℤ) := by
  intro p _ a hp2 hp4
  by_cases ha : a = 0
  · subst ha
    have hχ3 : ∀ x : ZMod p, quadraticChar (ZMod p) (x ^ 3) = quadraticChar (ZMod p) x := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · rcases quadraticChar_dichotomy hx with h | h <;>
          rw [show x ^ 3 = x * (x * x) by ring, map_mul, map_mul, h] <;> norm_num
    have hsum : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 0 * x + (0 : ZMod p)) = 0 := by
      have hx : ∀ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 0 * x + (0 : ZMod p)) =
          quadraticChar (ZMod p) x := by
        intro x
        simp only [zero_mul, add_zero]
        exact hχ3 x
      rw [Finset.sum_congr rfl (fun x _ => hx x)]
      exact quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    rw [hsum]
    norm_num
  · obtain ⟨ρ, hρ⟩ := lem258 p hp4
    have h259 := lem259 p a ρ hp2 hρ
    have h260 := lem260 p a ρ hp2 ha hρ
    have h261 := lem261 p ρ hρ
    set T := ∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) with hT
    have hconj : starRingEnd ℂ T =
        ∑ t : ZMod p, ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) := by
      rw [hT, map_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [map_mul, h261 t]
      simp
    have hsum : ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ) =
        ((2 * T.re : ℝ) : ℂ) := by
      rw [Int.cast_sum, h259, ← hconj, Complex.add_conj]
    have hSR : ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℝ) =
        2 * T.re := by
      exact_mod_cast hsum
    have hnorm : T.re * T.re + T.im * T.im = (p : ℝ) := by
      rw [← Complex.normSq_apply]
      exact h260
    have hR : ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℝ) ^ 2 ≤
        4 * (p : ℝ) := by
      rw [hSR]
      nlinarith [sq_nonneg T.im]
    exact_mod_cast hR

end MPP.Solutions.Bsd150
