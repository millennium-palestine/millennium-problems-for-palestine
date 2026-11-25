import Mathlib

namespace MPP.Solutions.Bsd186

theorem main : ∀ (p : ℕ) (A σ : ℝ) (u : ℕ → ℝ), p.Prime → 0 ≤ A → A * (p : ℝ) ^ (1 / 2 - σ) ≤ 1 / 2 →
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

end MPP.Solutions.Bsd186
