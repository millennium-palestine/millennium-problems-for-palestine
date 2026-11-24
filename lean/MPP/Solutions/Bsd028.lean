import Mathlib

namespace MPP.Solutions.Bsd028

-- the sequence satisfies c_{k+1} − β c_k = α^{k+1}, where α, β are the complex roots of z² − a z + p
theorem key_identity (a p : ℝ) (c : ℕ → ℝ) (α β : ℂ) (hsum : α + β = (a : ℂ))
    (hprod : α * β = (p : ℂ)) (h0 : c 0 = 1) (h1 : c 1 = a)
    (hrec : ∀ k : ℕ, c (k + 2) = a * c (k + 1) - p * c k) :
    ∀ k : ℕ, (c (k + 1) : ℂ) - β * (c k : ℂ) = α ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp [h0, h1]
    linear_combination -hsum
  | succ n ih =>
    have hr : (c (n + 2) : ℂ) = (a : ℂ) * (c (n + 1) : ℂ) - (p : ℂ) * (c n : ℂ) := by
      rw [hrec n]
      push_cast
      ring
    show (c (n + 2) : ℂ) - β * (c (n + 1) : ℂ) = α ^ (n + 2)
    linear_combination hr - (c (n + 1) : ℂ) * hsum + (c n : ℂ) * hprod + α * ih

theorem main : ∀ (a p : ℝ) (c : ℕ → ℝ), 0 ≤ p → a ^ 2 ≤ 4 * p → c 0 = 1 → c 1 = a →
    (∀ k : ℕ, c (k + 2) = a * c (k + 1) - p * c k) →
    ∀ k : ℕ, |c k| ≤ ((k : ℝ) + 1) * Real.sqrt p ^ k := by
  intro a p c hp ha h0 h1 hrec
  have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hr2 : Real.sqrt (4 * p - a ^ 2) ^ 2 = 4 * p - a ^ 2 := Real.sq_sqrt (by linarith)
  -- the two complex roots of z² − a z + p
  let α : ℂ := ⟨a / 2, Real.sqrt (4 * p - a ^ 2) / 2⟩
  let β : ℂ := ⟨a / 2, -(Real.sqrt (4 * p - a ^ 2) / 2)⟩
  have hsum : α + β = (a : ℂ) := by
    apply Complex.ext
    · simp [α, β]
    · simp [α, β]
  have hprod : α * β = (p : ℂ) := by
    apply Complex.ext
    · simp [α, β]
      linear_combination (1 / 4 : ℝ) * hr2
    · simp [α, β]
      ring
  -- both roots have modulus √p
  have hnorm : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = p → ‖z‖ = Real.sqrt p := by
    intro z hz
    rw [← Real.sqrt_sq (norm_nonneg z), Complex.sq_norm, Complex.normSq_apply]
    congr 1
    nlinarith [hz]
  have hα : ‖α‖ = Real.sqrt p := by
    apply hnorm
    simp only [α]
    linear_combination (1 / 4 : ℝ) * hr2
  have hβ : ‖β‖ = Real.sqrt p := by
    apply hnorm
    simp only [β]
    linear_combination (1 / 4 : ℝ) * hr2
  have key := key_identity a p c α β hsum hprod h0 h1 hrec
  -- |c_{k+1}| ≤ √p |c_k| + √p^{k+1}
  have hstep : ∀ k : ℕ, |c (k + 1)| ≤ Real.sqrt p * |c k| + Real.sqrt p ^ (k + 1) := by
    intro k
    have e : (c (k + 1) : ℂ) = β * (c k : ℂ) + α ^ (k + 1) := by
      linear_combination key k
    have hn : ‖(c (k + 1) : ℂ)‖ ≤ ‖β‖ * ‖(c k : ℂ)‖ + ‖α‖ ^ (k + 1) := by
      rw [e]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hα, hβ] at hn
    exact hn
  intro k
  induction k with
  | zero => simp [h0]
  | succ n ih =>
    calc |c (n + 1)| ≤ Real.sqrt p * |c n| + Real.sqrt p ^ (n + 1) := hstep n
      _ ≤ Real.sqrt p * (((n : ℝ) + 1) * Real.sqrt p ^ n) + Real.sqrt p ^ (n + 1) := by
        gcongr
      _ = (((n + 1 : ℕ) : ℝ) + 1) * Real.sqrt p ^ (n + 1) := by
        push_cast
        ring

end MPP.Solutions.Bsd028
