import Mathlib

namespace MPP.Solutions.Bsd258

theorem main : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 1 →
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

end MPP.Solutions.Bsd258
