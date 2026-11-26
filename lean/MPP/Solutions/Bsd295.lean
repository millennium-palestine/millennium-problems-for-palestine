import Mathlib

namespace MPP.Solutions.Bsd295

/-- preΨ′ 5 and the discriminant depend only on the four b-invariants. -/
lemma eq_of_b {K : Type} [Field K] (W W' : WeierstrassCurve K)
    (hb2 : W'.b₂ = W.b₂) (hb4 : W'.b₄ = W.b₄) (hb6 : W'.b₆ = W.b₆) (hb8 : W'.b₈ = W.b₈) :
    W'.Δ = W.Δ ∧ W'.preΨ' 5 = W.preΨ' 5 := by
  constructor
  · simp only [WeierstrassCurve.Δ, hb2, hb4, hb6, hb8]
  · simp only [WeierstrassCurve.preΨ', WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.preΨ₄, hb2, hb4, hb6, hb8]

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    (2 : K) ≠ 0 →
    ∃ W' : WeierstrassCurve K, W'.a₁ = 0 ∧ W'.a₃ = 0 ∧ W'.Δ = W.Δ ∧ W'.preΨ' 5 = W.preΨ' 5 := by
  intro K _ W h2
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  let W' : WeierstrassCurve K :=
    ⟨0, W.a₂ + W.a₁ ^ 2 / 4, 0, W.a₄ + W.a₁ * W.a₃ / 2, W.a₆ + W.a₃ ^ 2 / 4⟩
  have hb2 : W'.b₂ = W.b₂ := by
    simp only [W', WeierstrassCurve.b₂]
    field_simp
    ring
  have hb4 : W'.b₄ = W.b₄ := by
    simp only [W', WeierstrassCurve.b₄]
    field_simp
    ring
  have hb6 : W'.b₆ = W.b₆ := by
    simp only [W', WeierstrassCurve.b₆]
    field_simp
    ring
  have hb8 : W'.b₈ = W.b₈ := by
    apply mul_left_cancel₀ h4
    rw [W'.b_relation, hb2, hb4, hb6, W.b_relation]
  obtain ⟨hΔ, hpre⟩ := eq_of_b W W' hb2 hb4 hb6 hb8
  exact ⟨W', rfl, rfl, hΔ, hpre⟩

end MPP.Solutions.Bsd295
