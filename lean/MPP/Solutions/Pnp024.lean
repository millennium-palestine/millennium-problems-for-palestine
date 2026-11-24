import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp022
import MPP.Solutions.Pnp023
import MPP.Solutions.Pnp027

namespace MPP.Solutions.Pnp024

open MPP.PvsNP Turing

/-- A polynomial with natural coefficients is monotone on `ℕ`. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

theorem main : ∀ S L : Lang, InNP S →
    (∃ f : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
        ∀ x, L x = S (f x)) →
    InNP L := by
  intro S L hS hf
  obtain ⟨f, hf0, hLf⟩ := hf
  obtain ⟨V, hV, p, hp⟩ := hS
  obtain ⟨r, ⟨hr⟩, hrz⟩ := MPP.Solutions.Pnp022.main f hf0
  obtain ⟨q, hq⟩ := MPP.Solutions.Pnp023.main f hf0
  obtain ⟨C, hC, hCiff⟩ := MPP.Solutions.Pnp027.main p
  have hVr : InP (fun z => V (r z)) := MPP.Solutions.Pnp008.main V r hV hr
  have hCr : InP (fun z => C (r z)) := MPP.Solutions.Pnp008.main C r hC hr
  refine ⟨fun z => V (r z) && C (r z), MPP.Solutions.Pnp011.main _ _ hVr hCr, p.comp q, ?_⟩
  intro x
  rw [hLf x]
  constructor
  · intro hSf
    obtain ⟨w, hwlen, hVw⟩ := (hp (f x)).1 hSf
    refine ⟨w, ?_, ?_⟩
    · rw [Polynomial.eval_comp]
      exact le_trans hwlen (eval_mono p (hq x))
    · simp only [hrz, Bool.and_eq_true]
      exact ⟨hVw, (hCiff (f x) w).2 hwlen⟩
  · rintro ⟨w, -, hw⟩
    simp only [hrz, Bool.and_eq_true] at hw
    apply (hp (f x)).2
    exact ⟨w, (hCiff (f x) w).1 hw.2, hw.1⟩

end MPP.Solutions.Pnp024
