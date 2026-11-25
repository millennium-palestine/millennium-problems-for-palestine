import Mathlib

namespace MPP.Solutions.Bsd235

theorem main : ∀ (G : Type) [AddCommGroup G] (ℓ k : ℕ), Nat.Coprime ℓ k →
    Nat.card {x : G // ℓ • x = 0} * Nat.card {x : G // k • x = 0} ≤ Nat.card {x : G // (ℓ * k) • x = 0} := by
  intro G _ ℓ k hcop
  obtain ⟨a, b, hab⟩ : IsCoprime (ℓ : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  by_cases hA : Finite {x : G // ℓ • x = 0}
  · by_cases hB : Finite {x : G // k • x = 0}
    · let f : {x : G // ℓ • x = 0} × {x : G // k • x = 0} → {x : G // (ℓ * k) • x = 0} :=
        fun pq => ⟨pq.1.1 + pq.2.1, by
          have h1 : (ℓ * k) • pq.1.1 = 0 := by rw [mul_comm, mul_smul, pq.1.2, smul_zero]
          have h2 : (ℓ * k) • pq.2.1 = 0 := by rw [mul_smul, pq.2.2, smul_zero]
          rw [smul_add, h1, h2, add_zero]⟩
      have hinj : Function.Injective f := by
        rintro ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ ⟨⟨P', hP'⟩, ⟨Q', hQ'⟩⟩ h
        have h' : P + Q = P' + Q' := congrArg Subtype.val h
        have hT : P - P' = Q' - Q := by
          rw [sub_eq_sub_iff_add_eq_add, h', add_comm]
        have hℓT : ℓ • (P - P') = 0 := by rw [smul_sub, hP, hP', sub_zero]
        have hkT : k • (P - P') = 0 := by rw [hT, smul_sub, hQ', hQ, sub_zero]
        have hT0 : P - P' = 0 := by
          calc P - P' = (a * (ℓ : ℤ) + b * (k : ℤ)) • (P - P') := by rw [hab, one_smul]
            _ = a • (ℓ • (P - P')) + b • (k • (P - P')) := by
              rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
            _ = 0 := by rw [hℓT, hkT, smul_zero, smul_zero, add_zero]
        have hPP : P = P' := sub_eq_zero.mp hT0
        have hQQ : Q = Q' := (sub_eq_zero.mp (hT.symm.trans hT0)).symm
        subst hPP
        subst hQQ
        rfl
      have hsurj : Function.Surjective f := by
        rintro ⟨R, hR⟩
        have h1 : ℓ • ((b * k : ℤ) • R) = 0 := by
          rw [← natCast_zsmul, ← mul_smul, show (ℓ : ℤ) * (b * k) = b * ((ℓ * k : ℕ) : ℤ) by push_cast; ring,
            mul_smul, natCast_zsmul, hR, smul_zero]
        have h2 : k • ((a * ℓ : ℤ) • R) = 0 := by
          rw [← natCast_zsmul, ← mul_smul, show (k : ℤ) * (a * ℓ) = a * ((ℓ * k : ℕ) : ℤ) by push_cast; ring,
            mul_smul, natCast_zsmul, hR, smul_zero]
        refine ⟨(⟨(b * k : ℤ) • R, h1⟩, ⟨(a * ℓ : ℤ) • R, h2⟩), ?_⟩
        apply Subtype.ext
        show (b * k : ℤ) • R + (a * ℓ : ℤ) • R = R
        rw [← add_smul, show (b * k : ℤ) + a * ℓ = 1 by linarith, one_smul]
      have hfin : Finite {x : G // (ℓ * k) • x = 0} := Finite.of_surjective f hsurj
      rw [← Nat.card_prod]
      exact Nat.card_le_card_of_injective f hinj
    · haveI := not_finite_iff_infinite.mp hB
      have : Nat.card {x : G // k • x = 0} = 0 := Nat.card_eq_zero_of_infinite
      rw [this, mul_zero]
      exact Nat.zero_le _
  · haveI := not_finite_iff_infinite.mp hA
    have : Nat.card {x : G // ℓ • x = 0} = 0 := Nat.card_eq_zero_of_infinite
    rw [this, zero_mul]
    exact Nat.zero_le _

end MPP.Solutions.Bsd235
