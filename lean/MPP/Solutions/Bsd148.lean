import Mathlib

namespace MPP.Solutions.Bsd148

open Finset

section Basic

variable {p : ℕ} [Fact p.Prime]

lemma psi_pow_apply (ψ : MulChar (ZMod p) ℂ) (x : ZMod p) (n : ℕ) : ψ (x ^ n) = ψ x ^ n := by
  induction n with
  | zero => simp [MulChar.map_one]
  | succ n ih => rw [pow_succ, pow_succ, map_mul, ih]

lemma exists_prim_cube (h : p % 3 = 1) : ∃ ζ : ZMod p, IsPrimitiveRoot ζ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  refine ⟨(g : ZMod p), ?_⟩
  have h3 : IsPrimitiveRoot (g : ZMod p) (orderOf (g : ZMod p)) := IsPrimitiveRoot.orderOf _
  rwa [orderOf_units, hg] at h3

lemma fiber_card (ζ : ZMod p) (hζ : IsPrimitiveRoot ζ 3) (x0 : ZMod p) (hx0 : x0 ≠ 0) :
    (univ.filter (fun x : ZMod p => x ^ 3 = x0 ^ 3)).card = 3 := by
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  rw [Finset.card_eq_three]
  refine ⟨x0, x0 * ζ, x0 * ζ ^ 2, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hx0
    have : x0 * (ζ - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hζ1
  · intro h
    apply hx0
    have : x0 * (1 - ζ ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h').symm hζ2
  · intro h
    have : x0 * ζ * (1 - ζ) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hx0 h''
      · exact hζ0 h''
    · exact hζ1 (sub_eq_zero.mp h').symm
  · ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hx
      have hy : (x * x0⁻¹) ^ 3 = 1 := by
        rw [mul_pow, inv_pow, hx, mul_inv_cancel₀ (pow_ne_zero 3 hx0)]
      obtain ⟨i, hi, hiz⟩ := hζ.eq_pow_of_pow_eq_one hy
      have hx' : x = x0 * ζ ^ i := by
        rw [hiz]
        field_simp
      interval_cases i
      · left; simpa using hx'
      · right; left; simpa using hx'
      · right; right; simpa using hx'
    · rintro (rfl | rfl | rfl)
      · rfl
      · linear_combination x0 ^ 3 * hζ3
      · linear_combination x0 ^ 3 * (ζ ^ 3 + 1) * hζ3


lemma cube_of_char_one (ψ : MulChar (ZMod p) ℂ) (hψ3 : ψ ^ 3 = 1) (hψ1 : ψ ≠ 1) (u : ZMod p)
    (hu : u ≠ 0) (hψu : ψ u = 1) : ∃ x0 : ZMod p, x0 ≠ 0 ∧ x0 ^ 3 = u := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hpow : ∀ m : ℕ, ψ ((g ^ m : (ZMod p)ˣ) : ZMod p) = ψ (g : ZMod p) ^ m := by
    intro m
    have := MulChar.coe_toUnitHom ψ (g ^ m)
    rw [map_pow] at this
    rw [← this, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom]
  have hg1 : ψ (g : ZMod p) ≠ 1 := by
    intro h1
    apply hψ1
    apply MulChar.ext
    intro a
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg a))
    rw [hpow m, h1, one_pow, MulChar.one_apply_coe]
  have h3g : ψ (g : ZMod p) ^ 3 = 1 := by
    have := MulChar.pow_apply_coe ψ 3 g
    rw [hψ3, MulChar.one_apply_coe] at this
    exact this.symm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (ψ (g : ZMod p)) = 3 := orderOf_eq_prime h3g hg1
  let U : (ZMod p)ˣ := Units.mk0 u hu
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg U))
  have hm1 : ψ (g : ZMod p) ^ m = 1 := by
    rw [← hpow m, hm]
    exact hψu
  have h3m : 3 ∣ m := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hm1
  obtain ⟨k, rfl⟩ := h3m
  refine ⟨((g ^ k : (ZMod p)ˣ) : ZMod p), (g ^ k).ne_zero, ?_⟩
  have hcube : ((g ^ k : (ZMod p)ˣ) : ZMod p) ^ 3 = ((g ^ (3 * k) : (ZMod p)ˣ) : ZMod p) := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
  rw [hcube, hm]
  rfl


lemma count_eq (ψ : MulChar (ZMod p) ℂ) (hψ3 : ψ ^ 3 = 1) (hψ1 : ψ ≠ 1) (hp3 : p % 3 = 1)
    (u : ZMod p) :
    ((univ.filter (fun x : ZMod p => x ^ 3 = u)).card : ℂ) =
      (if u = 0 then 1 else 0) + ∑ j ∈ range 3, (ψ ^ j) u := by
  obtain ⟨ζ, hζ⟩ := exists_prim_cube hp3
  have hsum3 : ∀ x : ZMod p, IsUnit x → ψ x ^ 3 = 1 := by
    intro x hx
    have := MulChar.pow_apply' ψ (by norm_num : (3 : ℕ) ≠ 0) x
    rw [hψ3, MulChar.one_apply hx] at this
    exact this.symm
  by_cases hu0 : u = 0
  · subst hu0
    have hset : univ.filter (fun x : ZMod p => x ^ 3 = 0) = {0} := by
      ext x
      simp
    rw [hset]
    simp [MulChar.map_zero]
  · have hu : IsUnit u := isUnit_iff_ne_zero.mpr hu0
    have hsum : ∑ j ∈ range 3, (ψ ^ j) u = 1 + ψ u + ψ u ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
        MulChar.one_apply hu, pow_one, MulChar.pow_apply' ψ (by norm_num : (2 : ℕ) ≠ 0) u]
    rw [hsum, if_neg hu0, zero_add]
    by_cases hz : ψ u = 1
    · obtain ⟨x0, hx0, hx0u⟩ := cube_of_char_one ψ hψ3 hψ1 u hu0 hz
      subst hx0u
      rw [fiber_card ζ hζ x0 hx0]
      norm_num [hz]
    · have hcard : univ.filter (fun x : ZMod p => x ^ 3 = u) = ∅ := by
        ext x
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hu0 (by rw [← hx]; simp)
        apply hz
        rw [← hx, psi_pow_apply]
        exact hsum3 x (isUnit_iff_ne_zero.mpr hx0)
      have key : 1 + ψ u + ψ u ^ 2 = 0 := by
        have h1 : (ψ u - 1) * (1 + ψ u + ψ u ^ 2) = 0 := by
          linear_combination hsum3 u hu
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd (sub_eq_zero.mp h) hz
        · exact h
      rw [hcard, card_empty, key]
      simp

/-- The quadratic character with values in ℂ. -/
def phiC : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma phiC_apply (x : ZMod p) : phiC x = ((quadraticChar (ZMod p) x : ℤ) : ℂ) := by
  simp [phiC]

lemma phiC_conj (x : ZMod p) : (starRingEnd ℂ) (phiC x) = phiC x := by
  rw [phiC_apply, map_intCast]

lemma phiC_mul_self : phiC * phiC = (1 : MulChar (ZMod p) ℂ) := by
  refine MulChar.ext' fun a => ?_
  by_cases ha : IsUnit a
  · have h := quadraticChar_sq_one (F := ZMod p) (a := a) (isUnit_iff_ne_zero.mp ha)
    simp only [MulChar.coeToFun_mul, Pi.mul_apply, MulChar.one_apply ha, phiC_apply]
    have h' : ((quadraticChar (ZMod p) a : ℤ) : ℂ) * ((quadraticChar (ZMod p) a : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← pow_two, h]
      simp
    exact h'
  · simp only [MulChar.coeToFun_mul, Pi.mul_apply]
    rw [MulChar.map_nonunit phiC ha, MulChar.map_nonunit (1 : MulChar (ZMod p) ℂ) ha, zero_mul]

lemma phiC_ne_one (hp2 : p ≠ 2) : (phiC : MulChar (ZMod p) ℂ) ≠ 1 := by
  intro h
  unfold phiC at h
  have h' := (MulChar.ringHomComp_eq_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mp h
  exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact hp2) h'

lemma cube_unit (ψ : MulChar (ZMod p) ℂ) (h3 : ψ ^ 3 = 1) (v : ZMod p) (hv : IsUnit v) :
    ψ v ^ 3 = 1 := by
  have := MulChar.pow_apply' ψ (by norm_num : (3 : ℕ) ≠ 0) v
  rw [h3, MulChar.one_apply hv] at this
  exact this.symm

lemma prod_ne_one (χ : MulChar (ZMod p) ℂ) (h3 : χ ^ 3 = 1) (h1 : χ ≠ 1) (hp2 : p ≠ 2) :
    χ * phiC ≠ 1 := by
  intro h
  have hχ : χ = phiC := by
    calc χ = χ * (phiC * phiC) := by rw [phiC_mul_self, mul_one]
      _ = (χ * phiC) * phiC := (mul_assoc _ _ _).symm
      _ = phiC := by rw [h, one_mul]
  apply h1
  have h2 : χ ^ 2 = 1 := by rw [hχ, pow_two, phiC_mul_self]
  calc χ = χ ^ 2 * χ := by rw [h2, one_mul]
    _ = χ ^ 3 := (pow_succ χ 2).symm
    _ = 1 := h3

lemma psi_inv_eq (ψ : MulChar (ZMod p) ℂ) (h3 : ψ ^ 3 = 1) : ψ⁻¹ = ψ ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h3])

lemma conj_psi (ψ : MulChar (ZMod p) ℂ) (v : ZMod p) : (starRingEnd ℂ) (ψ v) = ψ⁻¹ v := by
  have := MulChar.star_apply' ψ v
  simpa [Complex.star_def] using this

lemma jac_conj (ψ : MulChar (ZMod p) ℂ) :
    (starRingEnd ℂ) (jacobiSum ψ phiC) = jacobiSum ψ⁻¹ phiC := by
  unfold jacobiSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, conj_psi, phiC_conj]

lemma jac_prod (ψ : MulChar (ZMod p) ℂ) (h3 : ψ ^ 3 = 1) (h1 : ψ ≠ 1) (hp2 : p ≠ 2) :
    jacobiSum ψ phiC * jacobiSum ψ⁻¹ phiC = (p : ℂ) := by
  have hc : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq_zero]
    have hpp : p.Prime := Fact.out
    exact hpp.ne_zero.symm
  have hφinv : (phiC : MulChar (ZMod p) ℂ)⁻¹ = phiC := inv_eq_of_mul_eq_one_right phiC_mul_self
  have := jacobiSum_mul_jacobiSum_inv hc h1 (phiC_ne_one hp2) (prod_ne_one ψ h3 h1 hp2)
  rw [hφinv] at this
  rw [this, ZMod.card]

lemma phiC_sq (b : ZMod p) (hb : b ≠ 0) : phiC b * phiC b = 1 := by
  have := congrArg (fun χ : MulChar (ZMod p) ℂ => χ b) phiC_mul_self
  simp only [MulChar.coeToFun_mul, Pi.mul_apply, MulChar.one_apply (isUnit_iff_ne_zero.mpr hb)] at this
  exact this

lemma shift (χ : MulChar (ZMod p) ℂ) (b : ZMod p) (hb : b ≠ 0) :
    ∑ u, χ u * phiC (u + b) = χ (-b) * phiC b * jacobiSum χ phiC := by
  have hnb : -b ≠ 0 := neg_ne_zero.mpr hb
  unfold jacobiSum
  rw [Finset.mul_sum]
  calc ∑ u, χ u * phiC (u + b) = ∑ t, χ (-b * t) * phiC (-b * t + b) :=
        (Equiv.sum_comp (Equiv.mulLeft₀ (-b) hnb) (fun u => χ u * phiC (u + b))).symm
    _ = ∑ t, χ (-b) * phiC b * (χ t * phiC (1 - t)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [show -b * t + b = b * (1 - t) by ring, map_mul χ, map_mul phiC]
        ring

lemma shift0 (χ : MulChar (ZMod p) ℂ) (hχ : χ * phiC ≠ 1) :
    ∑ u, χ u * phiC (u + 0) = 0 := by
  simp only [add_zero]
  have h : ∀ u, χ u * phiC u = (χ * phiC : MulChar (ZMod p) ℂ) u := fun u => by
    rw [MulChar.coeToFun_mul, Pi.mul_apply]
  simp only [h]
  exact MulChar.sum_eq_zero_of_ne_one hχ

lemma sum_phi_shift (b : ZMod p) (hp2 : p ≠ 2) : ∑ u, phiC (u + b) = 0 := by
  have : ∑ u, phiC (u + b) = ∑ z, phiC z := Equiv.sum_comp (Equiv.addRight b) (fun z => phiC z)
  rw [this]
  simp only [phiC_apply]
  rw [← Int.cast_sum, quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)]
  simp

lemma one_part (b : ZMod p) (hp2 : p ≠ 2) :
    ∑ u, (1 : MulChar (ZMod p) ℂ) u * phiC (u + b) = -phiC b := by
  have h1 : ∀ u : ZMod p, (1 : MulChar (ZMod p) ℂ) u = 1 - (if u = 0 then 1 else 0) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [MulChar.map_zero]
    · rw [if_neg hu, sub_zero]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)
  simp only [h1, sub_mul, one_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' univ (0 : ZMod p), sum_phi_shift b hp2]
  simp

lemma final_bound (p : ℕ) (S : ℤ) (w : ℂ) (hS : (S : ℂ) = w + starRingEnd ℂ w)
    (hw : w * starRingEnd ℂ w = (p : ℂ)) : S ^ 2 ≤ 4 * (p : ℤ) := by
  have hre : w + starRingEnd ℂ w = ((2 * w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have hS' : (S : ℝ) = 2 * w.re := by
    have h := congrArg Complex.re (hS.trans hre)
    simpa using h
  have hn : w.re * w.re + w.im * w.im = (p : ℝ) := by
    have h := congrArg Complex.re hw
    have h2 : (p : ℂ).re = (p : ℝ) := by simp
    simp [Complex.mul_re] at h
    linarith [h, h2]
  have key : (S : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
    rw [hS']
    nlinarith [mul_self_nonneg w.im]
  have key' : ((S ^ 2 : ℤ) : ℝ) ≤ ((4 * (p : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith [key]
  exact_mod_cast key'

lemma psi_mul_inv_unit (ψ : MulChar (ZMod p) ℂ) (h3 : ψ ^ 3 = 1) (v : ZMod p) (hv : IsUnit v) :
    ψ v * ψ⁻¹ v = 1 := by
  rw [psi_inv_eq ψ h3, MulChar.pow_apply' ψ (by norm_num : (2 : ℕ) ≠ 0) v]
  calc ψ v * ψ v ^ 2 = ψ v ^ 3 := by ring
    _ = 1 := cube_unit ψ h3 v hv

theorem bound_main (ψ : MulChar (ZMod p) ℂ) (h3 : ψ ^ 3 = 1) (h1 : ψ ≠ 1) (hp2 : p ≠ 2)
    (hp3 : p % 3 = 1) (b : ZMod p) :
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + b)) ^ 2 ≤ 4 * (p : ℤ) := by
  have hS1 : ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + b) : ℤ) : ℂ) =
      ∑ x : ZMod p, phiC (x ^ 3 + b) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [phiC_apply, zero_mul, add_zero]
  have hS2 : ∑ x : ZMod p, phiC (x ^ 3 + b) =
      ∑ u : ZMod p, ((univ.filter (fun x : ZMod p => x ^ 3 = u)).card : ℂ) * phiC (u + b) := by
    rw [← Finset.sum_fiberwise univ (fun x : ZMod p => x ^ 3)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => phiC (u + b)) (fun x hx => by rw [(mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hS3 : ∑ u : ZMod p, ((univ.filter (fun x : ZMod p => x ^ 3 = u)).card : ℂ) * phiC (u + b) =
      phiC b + ∑ j ∈ range 3, ∑ u : ZMod p, (ψ ^ j) u * phiC (u + b) := by
    have hc : ∀ u : ZMod p, ((univ.filter (fun x : ZMod p => x ^ 3 = u)).card : ℂ) * phiC (u + b) =
        (if u = 0 then phiC (u + b) else 0) + ∑ j ∈ range 3, (ψ ^ j) u * phiC (u + b) := by
      intro u
      rw [count_eq ψ h3 h1 hp3 u, add_mul, Finset.sum_mul]
      by_cases hu : u = 0 <;> simp [hu]
    rw [Finset.sum_congr rfl (fun u _ => hc u), Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    simp
  have hsplit : ∑ j ∈ range 3, ∑ u : ZMod p, (ψ ^ j) u * phiC (u + b) =
      (∑ u : ZMod p, (1 : MulChar (ZMod p) ℂ) u * phiC (u + b)) +
        (∑ u : ZMod p, ψ u * phiC (u + b)) + (∑ u : ZMod p, ψ⁻¹ u * phiC (u + b)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      ← psi_inv_eq ψ h3]
  have hS : ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + b) : ℤ) : ℂ) =
      (∑ u : ZMod p, ψ u * phiC (u + b)) + (∑ u : ZMod p, ψ⁻¹ u * phiC (u + b)) := by
    rw [hS1, hS2, hS3, hsplit, one_part b hp2]
    ring
  by_cases hb : b = 0
  · subst hb
    have h3' : ψ⁻¹ ^ 3 = 1 := by rw [inv_pow, h3, inv_one]
    have hz1 : ∑ u : ZMod p, ψ u * phiC (u + 0) = 0 := shift0 ψ (prod_ne_one ψ h3 h1 hp2)
    have hz2 : ∑ u : ZMod p, ψ⁻¹ u * phiC (u + 0) = 0 :=
      shift0 ψ⁻¹ (prod_ne_one ψ⁻¹ h3' (inv_ne_one.mpr h1) hp2)
    rw [hz1, hz2, add_zero] at hS
    have hS0 : (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + 0)) = 0 := by
      exact_mod_cast hS
    rw [hS0]
    norm_num
  · have hu : IsUnit (-b) := isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hb)
    rw [shift ψ b hb, shift ψ⁻¹ b hb] at hS
    refine final_bound p _ (ψ (-b) * phiC b * jacobiSum ψ phiC) ?_ ?_
    · rw [hS, map_mul, map_mul, conj_psi, phiC_conj, jac_conj]
    · rw [map_mul, map_mul, conj_psi, phiC_conj, jac_conj]
      calc _ = (ψ (-b) * ψ⁻¹ (-b)) * (phiC b * phiC b) * (jacobiSum ψ phiC * jacobiSum ψ⁻¹ phiC) := by
            ring
        _ = (p : ℂ) := by
            rw [psi_mul_inv_unit ψ h3 (-b) hu, phiC_sq b hb, jac_prod ψ h3 h1 hp2, one_mul, one_mul]


end Basic

theorem main : ∀ (p : ℕ) [Fact p.Prime] (b : ZMod p), p ≠ 2 → p % 3 = 1 →
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + b)) ^ 2 ≤ 4 * (p : ℤ) := by
  intro p _ b hp2 hp3
  have hdvd : 3 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨ψ, hψord⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd (Complex.isPrimitiveRoot_exp 3 (by norm_num))
  have h3 : ψ ^ 3 = 1 := by
    rw [← hψord]
    exact pow_orderOf_eq_one ψ
  have h1 : ψ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hψord
    norm_num at hψord
  exact bound_main ψ h3 h1 hp2 hp3 b

end MPP.Solutions.Bsd148
