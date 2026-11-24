import Mathlib

namespace MPP.Solutions.Bsd144

open Finset

/-- A change of variables `x = u² x' + r`, `y = u³ y' + s u² x' + t` identifies the equation of the
transformed curve (coefficients `u⁻¹ (a₁ + 2s)`, ...) at `(x', y')` with the original equation. -/
theorem equation_transport (p : ℕ) [Fact p.Prime] (u r s t a₁ a₂ a₃ a₄ a₆ x y : ZMod p)
    (hu : u ≠ 0) :
    (y ^ 2 + (u⁻¹ * (a₁ + 2 * s)) * x * y + (u⁻¹ ^ 3 * (a₃ + r * a₁ + 2 * t)) * y =
        x ^ 3 + (u⁻¹ ^ 2 * (a₂ - s * a₁ + 3 * r - s ^ 2)) * x ^ 2 +
          (u⁻¹ ^ 4 * (a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t)) * x +
          u⁻¹ ^ 6 * (a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁)) ↔
      ((u ^ 3 * y + s * u ^ 2 * x + t) ^ 2 + a₁ * (u ^ 2 * x + r) * (u ^ 3 * y + s * u ^ 2 * x + t) +
          a₃ * (u ^ 3 * y + s * u ^ 2 * x + t) =
        (u ^ 2 * x + r) ^ 3 + a₂ * (u ^ 2 * x + r) ^ 2 + a₄ * (u ^ 2 * x + r) + a₆) := by
  have key : ((u ^ 3 * y + s * u ^ 2 * x + t) ^ 2 + a₁ * (u ^ 2 * x + r) * (u ^ 3 * y + s * u ^ 2 * x + t) +
          a₃ * (u ^ 3 * y + s * u ^ 2 * x + t) -
        ((u ^ 2 * x + r) ^ 3 + a₂ * (u ^ 2 * x + r) ^ 2 + a₄ * (u ^ 2 * x + r) + a₆)) =
      u ^ 6 * ((y ^ 2 + (u⁻¹ * (a₁ + 2 * s)) * x * y + (u⁻¹ ^ 3 * (a₃ + r * a₁ + 2 * t)) * y) -
        (x ^ 3 + (u⁻¹ ^ 2 * (a₂ - s * a₁ + 3 * r - s ^ 2)) * x ^ 2 +
          (u⁻¹ ^ 4 * (a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t)) * x +
          u⁻¹ ^ 6 * (a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁))) := by
    field_simp
    ring
  constructor
  · intro h
    have h0 := key
    rw [sub_eq_zero.mpr h, mul_zero] at h0
    exact sub_eq_zero.mp h0
  · intro h
    have h0 : u ^ 6 * ((y ^ 2 + (u⁻¹ * (a₁ + 2 * s)) * x * y + (u⁻¹ ^ 3 * (a₃ + r * a₁ + 2 * t)) * y) -
        (x ^ 3 + (u⁻¹ ^ 2 * (a₂ - s * a₁ + 3 * r - s ^ 2)) * x ^ 2 +
          (u⁻¹ ^ 4 * (a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t)) * x +
          u⁻¹ ^ 6 * (a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁))) = 0 := by
      rw [← key, sub_eq_zero.mpr h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 6 hu))

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic], p ≠ 2 → p ≠ 3 →
    ∃ a b : ZMod p, ∃ _ : (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).IsElliptic,
      Nat.card W.toAffine.Point = Nat.card (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Point := by
  intro p _ W _ hp2 hp3
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hd)
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  haveI : Invertible (3 : ZMod p) := invertibleOfNonzero h3
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_isShortNF W
  haveI := hC
  have hshape : C • W = WeierstrassCurve.mk 0 0 0 (C • W).a₄ (C • W).a₆ := by
    ext <;> simp
  have hu : (C.u : ZMod p) ≠ 0 := Units.ne_zero _
  let g : ZMod p × ZMod p ≃ ZMod p × ZMod p :=
    { toFun := fun q => ((C.u : ZMod p) ^ 2 * q.1 + C.r, (C.u : ZMod p) ^ 3 * q.2 + C.s * (C.u : ZMod p) ^ 2 * q.1 + C.t)
      invFun := fun q => ((q.1 - C.r) / (C.u : ZMod p) ^ 2, (q.2 - C.s * (q.1 - C.r) - C.t) / (C.u : ZMod p) ^ 3)
      left_inv := fun q => by
        ext <;> simp <;> field_simp <;> ring
      right_inv := fun q => by
        ext <;> simp <;> field_simp <;> ring }
  have hg : ∀ q : ZMod p × ZMod p, W.toAffine.Nonsingular (g q).1 (g q).2 ↔
      (C • W).toAffine.Nonsingular q.1 q.2 := by
    intro q
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, ← WeierstrassCurve.Affine.equation_iff_nonsingular,
      WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, Units.val_inv_eq_inv_val, g]
    exact (equation_transport p (C.u : ZMod p) C.r C.s C.t W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ q.1 q.2 hu).symm
  have hsub : Nat.card {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} =
      Nat.card {xy : ZMod p × ZMod p // (C • W).toAffine.Nonsingular xy.1 xy.2} :=
    Nat.card_congr (g.symm.subtypeEquiv fun a => by
      have := hg (g.symm a)
      rwa [g.apply_symm_apply] at this)
  have hcount : Nat.card W.toAffine.Point = Nat.card (C • W).toAffine.Point := by
    rw [Nat.card_congr (WeierstrassCurve.Affine.nonsingularPointEquiv W.toAffine),
      Nat.card_congr (WeierstrassCurve.Affine.nonsingularPointEquiv (C • W).toAffine)]
    exact Nat.card_congr ((g.symm.subtypeEquiv fun a => by
      have := hg (g.symm a)
      rwa [g.apply_symm_apply] at this).optionCongr)
  haveI : (C • W).IsElliptic := inferInstance
  refine ⟨(C • W).a₄, (C • W).a₆, ?_, ?_⟩
  · rw [← hshape]
    infer_instance
  · rw [← hshape]
    exact hcount

end MPP.Solutions.Bsd144
