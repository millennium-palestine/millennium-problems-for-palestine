import Mathlib

namespace MPP.Solutions.Bsd411

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (f : Polynomial K), f ≠ 0 →
    Set.ncard {P : K × K | P.2 ^ 2 + W.a₁ * P.1 * P.2 + W.a₃ * P.2 = P.1 ^ 3 + W.a₂ * P.1 ^ 2 + W.a₄ * P.1 + W.a₆ ∧
      f.eval P.1 = 0} ≤ 2 * f.natDegree := by
  intro K _ W f hf
  classical
  -- a fibre over one x-coordinate has no three distinct y-values
  have three : ∀ (x y₁ y₂ y₃ : K),
      y₁ ^ 2 + W.a₁ * x * y₁ + W.a₃ * y₁ = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ →
      y₂ ^ 2 + W.a₁ * x * y₂ + W.a₃ * y₂ = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ →
      y₃ ^ 2 + W.a₁ * x * y₃ + W.a₃ * y₃ = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ →
      y₁ ≠ y₂ → y₁ ≠ y₃ → y₂ ≠ y₃ → False := by
    intro x y₁ y₂ y₃ h1 h2 h3 d12 d13 d23
    have e2 : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x + W.a₃) = 0 := by linear_combination h1 - h2
    have e3 : (y₁ - y₃) * (y₁ + y₃ + W.a₁ * x + W.a₃) = 0 := by linear_combination h1 - h3
    have s2 : y₁ + y₂ + W.a₁ * x + W.a₃ = 0 := (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 d12)
    have s3 : y₁ + y₃ + W.a₁ * x + W.a₃ = 0 := (mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 d13)
    exact d23 (by linear_combination s2 - s3)
  by_contra hcon
  rw [not_le] at hcon
  have hfin : Set.Finite {P : K × K | P.2 ^ 2 + W.a₁ * P.1 * P.2 + W.a₃ * P.2 = P.1 ^ 3 + W.a₂ * P.1 ^ 2 + W.a₄ * P.1 + W.a₆ ∧
      f.eval P.1 = 0} :=
    Set.finite_of_ncard_ne_zero (by omega)
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcon
  have hS : ∀ P ∈ hfin.toFinset, P.2 ^ 2 + W.a₁ * P.1 * P.2 + W.a₃ * P.2 = P.1 ^ 3 + W.a₂ * P.1 ^ 2 + W.a₄ * P.1 + W.a₆ ∧
      f.eval P.1 = 0 := fun P hP => hfin.mem_toFinset.1 hP
  -- each fibre contributes at most two points
  have hfib : ∀ b ∈ hfin.toFinset.image Prod.fst,
      (hfin.toFinset.filter (fun P => P.1 = b)).card ≤ 2 := by
    intro b _
    by_contra hc
    rw [not_le] at hc
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.1 hc
    rw [Finset.mem_filter] at hp hq hr
    have ep : p.2 ^ 2 + W.a₁ * b * p.2 + W.a₃ * p.2 = b ^ 3 + W.a₂ * b ^ 2 + W.a₄ * b + W.a₆ := by
      have := (hS p hp.1).1
      rw [hp.2] at this
      exact this
    have eq' : q.2 ^ 2 + W.a₁ * b * q.2 + W.a₃ * q.2 = b ^ 3 + W.a₂ * b ^ 2 + W.a₄ * b + W.a₆ := by
      have := (hS q hq.1).1
      rw [hq.2] at this
      exact this
    have er : r.2 ^ 2 + W.a₁ * b * r.2 + W.a₃ * r.2 = b ^ 3 + W.a₂ * b ^ 2 + W.a₄ * b + W.a₆ := by
      have := (hS r hr.1).1
      rw [hr.2] at this
      exact this
    exact three b p.2 q.2 r.2 ep eq' er
      (fun h => hpq (Prod.ext (hp.2.trans hq.2.symm) h))
      (fun h => hpr (Prod.ext (hp.2.trans hr.2.symm) h))
      (fun h => hqr (Prod.ext (hq.2.trans hr.2.symm) h))
  -- the x-coordinates are roots of f, so there are at most natDegree f of them
  have himg : (hfin.toFinset.image Prod.fst).card ≤ f.natDegree := by
    calc (hfin.toFinset.image Prod.fst).card ≤ f.roots.toFinset.card := by
          apply Finset.card_le_card
          intro b hb
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hb
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
          exact (hS P hP).2
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
  have hcard := Finset.card_le_mul_card_image hfin.toFinset 2 hfib
  omega

end MPP.Solutions.Bsd411
