import Mathlib

namespace MPP.Solutions.Bsd410

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (x : K),
    Set.ncard {y : K | y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆} ≤ 2 := by
  intro K _ W x
  by_contra hcon
  rw [not_le] at hcon
  have hfin : Set.Finite {y : K | y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆} :=
    Set.finite_of_ncard_ne_zero (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).1 hcon
  simp only [Set.mem_setOf_eq] at ha hb hc
  -- two distinct roots of a monic quadratic sum to -(a₁ x + a₃)
  have h1 : (a - b) * (a + b + W.a₁ * x + W.a₃) = 0 := by linear_combination ha - hb
  have h2 : (a - c) * (a + c + W.a₁ * x + W.a₃) = 0 := by linear_combination ha - hc
  have s2 : a + b + W.a₁ * x + W.a₃ = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hab)
  have s3 : a + c + W.a₁ * x + W.a₃ = 0 := (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hac)
  exact hbc (by linear_combination s2 - s3)

end MPP.Solutions.Bsd410
