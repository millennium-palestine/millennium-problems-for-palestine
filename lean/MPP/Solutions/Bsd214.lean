import Mathlib

namespace MPP.Solutions.Bsd214

/-! The case n = 2 of the elliptic-net addition formula for `normEDS`:
`N(m+2) N(m-2) = N(m+1) N(m-1) N(2)^2 - N(3) N(1) N(m)^2`.
Proved first over a domain (where `b = N 2 ≠ 0` can be cancelled), by strong
induction on `m` with the even and odd recursions, then transferred to `W.ψ`. -/

section Universal

variable {A : Type*} [CommRing A] (b c d : A)

lemma odd_step (u : ℤ)
    (h1 : normEDS b c d (u + 1 + 2) * normEDS b c d (u + 1 - 2)
      - b ^ 2 * normEDS b c d (u + 1 + 1) * normEDS b c d (u + 1 - 1)
      + c * normEDS b c d (u + 1) ^ 2 = 0)
    (h2 : normEDS b c d (u + 2 + 2) * normEDS b c d (u + 2 - 2)
      - b ^ 2 * normEDS b c d (u + 2 + 1) * normEDS b c d (u + 2 - 1)
      + c * normEDS b c d (u + 2) ^ 2 = 0) :
    normEDS b c d (2 * u + 3 + 2) * normEDS b c d (2 * u + 3 - 2)
      - b ^ 2 * normEDS b c d (2 * u + 3 + 1) * normEDS b c d (2 * u + 3 - 1)
      + c * normEDS b c d (2 * u + 3) ^ 2 = 0 := by
  have h1' : normEDS b c d (u + 3) * normEDS b c d (u - 1)
      - b ^ 2 * normEDS b c d (u + 2) * normEDS b c d u
      + c * normEDS b c d (u + 1) ^ 2 = 0 := by
    have h := h1
    rw [show u + 1 + 2 = u + 3 by ring, show u + 1 - 2 = u - 1 by ring,
      show u + 1 + 1 = u + 2 by ring, show u + 1 - 1 = u by ring] at h
    exact h
  have h2' : normEDS b c d (u + 4) * normEDS b c d u
      - b ^ 2 * normEDS b c d (u + 3) * normEDS b c d (u + 1)
      + c * normEDS b c d (u + 2) ^ 2 = 0 := by
    have h := h2
    rw [show u + 2 + 2 = u + 4 by ring, show u + 2 - 2 = u by ring,
      show u + 2 + 1 = u + 3 by ring, show u + 2 - 1 = u + 1 by ring] at h
    exact h
  have hO5 : normEDS b c d (2 * u + 5) = normEDS b c d (u + 4) * normEDS b c d (u + 2) ^ 3
      - normEDS b c d (u + 1) * normEDS b c d (u + 3) ^ 3 := by
    have h := normEDS_odd b c d (u + 2)
    rw [show 2 * (u + 2) + 1 = 2 * u + 5 by ring, show u + 2 + 2 = u + 4 by ring,
      show u + 2 - 1 = u + 1 by ring, show u + 2 + 1 = u + 3 by ring] at h
    exact h
  have hO1 : normEDS b c d (2 * u + 1) = normEDS b c d (u + 2) * normEDS b c d u ^ 3
      - normEDS b c d (u - 1) * normEDS b c d (u + 1) ^ 3 := normEDS_odd b c d u
  have hO3 : normEDS b c d (2 * u + 3) = normEDS b c d (u + 3) * normEDS b c d (u + 1) ^ 3
      - normEDS b c d u * normEDS b c d (u + 2) ^ 3 := by
    have h := normEDS_odd b c d (u + 1)
    rw [show 2 * (u + 1) + 1 = 2 * u + 3 by ring, show u + 1 + 2 = u + 3 by ring,
      show u + 1 - 1 = u by ring, show u + 1 + 1 = u + 2 by ring] at h
    exact h
  have hE4 : normEDS b c d (2 * u + 4) * b = normEDS b c d (u + 1) ^ 2 * normEDS b c d (u + 2)
      * normEDS b c d (u + 4) - normEDS b c d u * normEDS b c d (u + 2)
      * normEDS b c d (u + 3) ^ 2 := by
    have h := normEDS_even b c d (u + 2)
    rw [show 2 * (u + 2) = 2 * u + 4 by ring, show u + 2 - 1 = u + 1 by ring,
      show u + 2 + 2 = u + 4 by ring, show u + 2 - 2 = u by ring,
      show u + 2 + 1 = u + 3 by ring] at h
    exact h
  have hE2 : normEDS b c d (2 * u + 2) * b = normEDS b c d u ^ 2 * normEDS b c d (u + 1)
      * normEDS b c d (u + 3) - normEDS b c d (u - 1) * normEDS b c d (u + 1)
      * normEDS b c d (u + 2) ^ 2 := by
    have h := normEDS_even b c d (u + 1)
    rw [show 2 * (u + 1) = 2 * u + 2 by ring, show u + 1 - 1 = u by ring,
      show u + 1 + 2 = u + 3 by ring, show u + 1 - 2 = u - 1 by ring,
      show u + 1 + 1 = u + 2 by ring] at h
    exact h
  rw [show 2 * u + 3 + 2 = 2 * u + 5 by ring, show 2 * u + 3 - 2 = 2 * u + 1 by ring,
    show 2 * u + 3 + 1 = 2 * u + 4 by ring, show 2 * u + 3 - 1 = 2 * u + 2 by ring]
  linear_combination normEDS b c d (2 * u + 1) * hO5
    + (normEDS b c d (u + 4) * normEDS b c d (u + 2) ^ 3
      - normEDS b c d (u + 1) * normEDS b c d (u + 3) ^ 3) * hO1
    - (normEDS b c d (2 * u + 2) * b) * hE4
    - (normEDS b c d (u + 1) ^ 2 * normEDS b c d (u + 2) * normEDS b c d (u + 4)
      - normEDS b c d u * normEDS b c d (u + 2) * normEDS b c d (u + 3) ^ 2) * hE2
    + c * (normEDS b c d (2 * u + 3) + (normEDS b c d (u + 3) * normEDS b c d (u + 1) ^ 3
      - normEDS b c d u * normEDS b c d (u + 2) ^ 3)) * hO3
    + (normEDS b c d (u + 1) ^ 4 * normEDS b c d (u + 3) ^ 2
      - normEDS b c d (u + 1) * normEDS b c d (u + 2) ^ 3 * normEDS b c d (u + 3)
        * normEDS b c d u) * h1'
    + (-(normEDS b c d (u + 1) ^ 3 * normEDS b c d (u + 2) * normEDS b c d (u + 3)
        * normEDS b c d u) + normEDS b c d (u + 2) ^ 4 * normEDS b c d u ^ 2) * h2'

lemma even_step [IsDomain A] (hb : b ≠ 0) (u : ℤ)
    (h1 : normEDS b c d (u + 1 + 2) * normEDS b c d (u + 1 - 2)
      - b ^ 2 * normEDS b c d (u + 1 + 1) * normEDS b c d (u + 1 - 1)
      + c * normEDS b c d (u + 1) ^ 2 = 0)
    (h2 : normEDS b c d (u + 2 + 2) * normEDS b c d (u + 2 - 2)
      - b ^ 2 * normEDS b c d (u + 2 + 1) * normEDS b c d (u + 2 - 1)
      + c * normEDS b c d (u + 2) ^ 2 = 0)
    (h3 : normEDS b c d (u + 3 + 2) * normEDS b c d (u + 3 - 2)
      - b ^ 2 * normEDS b c d (u + 3 + 1) * normEDS b c d (u + 3 - 1)
      + c * normEDS b c d (u + 3) ^ 2 = 0) :
    normEDS b c d (2 * u + 4 + 2) * normEDS b c d (2 * u + 4 - 2)
      - b ^ 2 * normEDS b c d (2 * u + 4 + 1) * normEDS b c d (2 * u + 4 - 1)
      + c * normEDS b c d (2 * u + 4) ^ 2 = 0 := by
  have h1' : normEDS b c d (u + 3) * normEDS b c d (u - 1)
      - b ^ 2 * normEDS b c d (u + 2) * normEDS b c d u
      + c * normEDS b c d (u + 1) ^ 2 = 0 := by
    have h := h1
    rw [show u + 1 + 2 = u + 3 by ring, show u + 1 - 2 = u - 1 by ring,
      show u + 1 + 1 = u + 2 by ring, show u + 1 - 1 = u by ring] at h
    exact h
  have h2' : normEDS b c d (u + 4) * normEDS b c d u
      - b ^ 2 * normEDS b c d (u + 3) * normEDS b c d (u + 1)
      + c * normEDS b c d (u + 2) ^ 2 = 0 := by
    have h := h2
    rw [show u + 2 + 2 = u + 4 by ring, show u + 2 - 2 = u by ring,
      show u + 2 + 1 = u + 3 by ring, show u + 2 - 1 = u + 1 by ring] at h
    exact h
  have h3' : normEDS b c d (u + 5) * normEDS b c d (u + 1)
      - b ^ 2 * normEDS b c d (u + 4) * normEDS b c d (u + 2)
      + c * normEDS b c d (u + 3) ^ 2 = 0 := by
    have h := h3
    rw [show u + 3 + 2 = u + 5 by ring, show u + 3 - 2 = u + 1 by ring,
      show u + 3 + 1 = u + 4 by ring, show u + 3 - 1 = u + 2 by ring] at h
    exact h
  have hA : normEDS b c d (2 * u + 6) * b = normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 3)
      * normEDS b c d (u + 5) - normEDS b c d (u + 1) * normEDS b c d (u + 3)
      * normEDS b c d (u + 4) ^ 2 := by
    have h := normEDS_even b c d (u + 3)
    rw [show 2 * (u + 3) = 2 * u + 6 by ring, show u + 3 - 1 = u + 2 by ring,
      show u + 3 + 2 = u + 5 by ring, show u + 3 - 2 = u + 1 by ring,
      show u + 3 + 1 = u + 4 by ring] at h
    exact h
  have hB : normEDS b c d (2 * u + 2) * b = normEDS b c d u ^ 2 * normEDS b c d (u + 1)
      * normEDS b c d (u + 3) - normEDS b c d (u - 1) * normEDS b c d (u + 1)
      * normEDS b c d (u + 2) ^ 2 := by
    have h := normEDS_even b c d (u + 1)
    rw [show 2 * (u + 1) = 2 * u + 2 by ring, show u + 1 - 1 = u by ring,
      show u + 1 + 2 = u + 3 by ring, show u + 1 - 2 = u - 1 by ring,
      show u + 1 + 1 = u + 2 by ring] at h
    exact h
  have hC : normEDS b c d (2 * u + 4) * b = normEDS b c d (u + 1) ^ 2 * normEDS b c d (u + 2)
      * normEDS b c d (u + 4) - normEDS b c d u * normEDS b c d (u + 2)
      * normEDS b c d (u + 3) ^ 2 := by
    have h := normEDS_even b c d (u + 2)
    rw [show 2 * (u + 2) = 2 * u + 4 by ring, show u + 2 - 1 = u + 1 by ring,
      show u + 2 + 2 = u + 4 by ring, show u + 2 - 2 = u by ring,
      show u + 2 + 1 = u + 3 by ring] at h
    exact h
  have hD : normEDS b c d (2 * u + 5) = normEDS b c d (u + 4) * normEDS b c d (u + 2) ^ 3
      - normEDS b c d (u + 1) * normEDS b c d (u + 3) ^ 3 := by
    have h := normEDS_odd b c d (u + 2)
    rw [show 2 * (u + 2) + 1 = 2 * u + 5 by ring, show u + 2 + 2 = u + 4 by ring,
      show u + 2 - 1 = u + 1 by ring, show u + 2 + 1 = u + 3 by ring] at h
    exact h
  have hE : normEDS b c d (2 * u + 3) = normEDS b c d (u + 3) * normEDS b c d (u + 1) ^ 3
      - normEDS b c d u * normEDS b c d (u + 2) ^ 3 := by
    have h := normEDS_odd b c d (u + 1)
    rw [show 2 * (u + 1) + 1 = 2 * u + 3 by ring, show u + 1 + 2 = u + 3 by ring,
      show u + 1 - 1 = u by ring, show u + 1 + 1 = u + 2 by ring] at h
    exact h
  have hsq : b ^ 2 * (normEDS b c d (2 * u + 6) * normEDS b c d (2 * u + 2)
      - b ^ 2 * normEDS b c d (2 * u + 5) * normEDS b c d (2 * u + 3)
      + c * normEDS b c d (2 * u + 4) ^ 2) = 0 := by
    linear_combination (normEDS b c d (2 * u + 2) * b) * hA
      + (normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 3) * normEDS b c d (u + 5)
        - normEDS b c d (u + 1) * normEDS b c d (u + 3) * normEDS b c d (u + 4) ^ 2) * hB
      - b ^ 4 * normEDS b c d (2 * u + 3) * hD
      - b ^ 4 * (normEDS b c d (u + 4) * normEDS b c d (u + 2) ^ 3
        - normEDS b c d (u + 1) * normEDS b c d (u + 3) ^ 3) * hE
      + c * (normEDS b c d (2 * u + 4) * b + (normEDS b c d (u + 1) ^ 2 * normEDS b c d (u + 2)
        * normEDS b c d (u + 4) - normEDS b c d u * normEDS b c d (u + 2)
        * normEDS b c d (u + 3) ^ 2)) * hC
      + (-(b ^ 2) * normEDS b c d (u + 2) ^ 5 * normEDS b c d (u + 4)
        + b ^ 2 * normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 3) ^ 3 * normEDS b c d (u + 1)
        - normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 3) ^ 2 * normEDS b c d (u + 4)
          * normEDS b c d u
        + normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 4) ^ 2 * normEDS b c d (u + 1) ^ 2) * h1'
      + (b ^ 2 * normEDS b c d (u + 2) ^ 3 * normEDS b c d (u + 4) * normEDS b c d (u + 1) ^ 2
        - b ^ 2 * normEDS b c d (u + 3) ^ 3 * normEDS b c d (u + 1) ^ 3
        + normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 3) ^ 3 * normEDS b c d (u - 1)
        - normEDS b c d (u + 3) ^ 2 * normEDS b c d (u + 4) * normEDS b c d (u + 1) ^ 2
          * normEDS b c d u) * h2'
      + (-(normEDS b c d (u + 2) ^ 4 * normEDS b c d (u + 3) * normEDS b c d (u - 1))
        + normEDS b c d (u + 2) ^ 2 * normEDS b c d (u + 3) ^ 2 * normEDS b c d u ^ 2) * h3'
  rw [show 2 * u + 4 + 2 = 2 * u + 6 by ring, show 2 * u + 4 - 2 = 2 * u + 2 by ring,
    show 2 * u + 4 + 1 = 2 * u + 5 by ring, show 2 * u + 4 - 1 = 2 * u + 3 by ring]
  exact (mul_eq_zero.mp hsq).resolve_left (pow_ne_zero 2 hb)

lemma base_zero : normEDS b c d (0 + 2) * normEDS b c d (0 - 2)
      - b ^ 2 * normEDS b c d (0 + 1) * normEDS b c d (0 - 1)
      + c * normEDS b c d 0 ^ 2 = 0 := by
  simp [normEDS_neg]
  ring

lemma base_one : normEDS b c d (1 + 2) * normEDS b c d (1 - 2)
      - b ^ 2 * normEDS b c d (1 + 1) * normEDS b c d (1 - 1)
      + c * normEDS b c d 1 ^ 2 = 0 := by
  simp

lemma base_two : normEDS b c d (2 + 2) * normEDS b c d (2 - 2)
      - b ^ 2 * normEDS b c d (2 + 1) * normEDS b c d (2 - 1)
      + c * normEDS b c d 2 ^ 2 = 0 := by
  simp
  ring

lemma core [IsDomain A] (hb : b ≠ 0) (k : ℕ) :
    normEDS b c d ((k : ℤ) + 2) * normEDS b c d ((k : ℤ) - 2)
      - b ^ 2 * normEDS b c d ((k : ℤ) + 1) * normEDS b c d ((k : ℤ) - 1)
      + c * normEDS b c d (k : ℤ) ^ 2 = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
    · rcases t with _ | _ | s
      · simpa using base_zero b c d
      · simpa using base_two b c d
      · have e : ((2 * (s + 1 + 1) : ℕ) : ℤ) = 2 * (s : ℤ) + 4 := by push_cast; ring
        rw [e]
        exact even_step b c d hb (s : ℤ)
          (by have h := ih (s + 1) (by omega); push_cast at h; exact h)
          (by have h := ih (s + 2) (by omega); push_cast at h; exact h)
          (by have h := ih (s + 3) (by omega); push_cast at h; exact h)
    · rcases t with _ | s
      · simpa using base_one b c d
      · have e : ((2 * (s + 1) + 1 : ℕ) : ℤ) = 2 * (s : ℤ) + 3 := by push_cast; ring
        rw [e]
        exact odd_step b c d (s : ℤ)
          (by have h := ih (s + 1) (by omega); push_cast at h; exact h)
          (by have h := ih (s + 2) (by omega); push_cast at h; exact h)

lemma univ [IsDomain A] (hb : b ≠ 0) (m : ℤ) :
    normEDS b c d (m + 2) * normEDS b c d (m - 2)
      - b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + c * normEDS b c d m ^ 2 = 0 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact core b c d hb k
  · have hk := core b c d hb k
    rw [show -(k : ℤ) + 2 = -((k : ℤ) - 2) by ring, show -(k : ℤ) - 2 = -((k : ℤ) + 2) by ring,
      show -(k : ℤ) + 1 = -((k : ℤ) - 1) by ring, show -(k : ℤ) - 1 = -((k : ℤ) + 1) by ring]
    simp only [normEDS_neg]
    linear_combination hk

end Universal

/-- The n = 2 addition formula for the bivariate division polynomials. -/
theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (m : ℤ),
    W.ψ (m + 2) * W.ψ (m - 2) =
      W.ψ (m + 1) * W.ψ (m - 1) * W.ψ 2 ^ 2 - W.ψ 3 * W.ψ 1 * W.ψ m ^ 2 := by
  intro K _ W m
  have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hu := univ (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1)
    (MvPolynomial.X 2) hb m
  have hf := congrArg (MvPolynomial.aeval
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄] : MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial (Polynomial K)) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  simp only [WeierstrassCurve.ψ, normEDS_one, normEDS_two, normEDS_three]
  linear_combination hf

end MPP.Solutions.Bsd214
