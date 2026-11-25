import Mathlib

namespace MPP.Solutions.Bsd259

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p) (ρ : MulChar (ZMod p) ℂ), p ≠ 2 →
    (∀ x : ZMod p, ρ x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ)) →
    ∑ x : ZMod p, ((quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ) =
      ∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) +
      ∑ t : ZMod p, ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) := by
  intro p _ a ρ hp2 hρ
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  -- the summand is a function of x * x
  have hstep : ∀ x : ZMod p,
      ((quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ) =
        ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) := by
    intro x
    have hx : x ^ 3 + a * x + (0 : ZMod p) = x * (x * x + a) := by ring
    rw [hx, map_mul (quadraticChar (ZMod p)) x (x * x + a), Int.cast_mul, map_mul ρ x x,
      ← hρ x]
    ring
  -- the number of square roots of t
  have hfib : ∀ t : ZMod p,
      ((Finset.univ.filter (fun x : ZMod p => x * x = t)).card : ℂ) =
        ((quadraticChar (ZMod p) t : ℤ) : ℂ) + 1 := by
    intro t
    have h := quadraticChar_card_sqrts hchar t
    simp only [Set.toFinset_setOf] at h
    have h' : Finset.univ.filter (fun x : ZMod p => x * x = t) =
        Finset.univ.filter (fun x : ZMod p => x ^ 2 = t) := by
      ext x
      simp [pow_two]
    rw [h']
    exact_mod_cast h
  calc ∑ x : ZMod p, ((quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) : ℤ) : ℂ)
      = ∑ x : ZMod p, ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) :=
        Finset.sum_congr rfl (fun x _ => hstep x)
    _ = ∑ t : ZMod p, ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x * x = t),
          ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) :=
        (Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x * x) _).symm
    _ = ∑ t : ZMod p, ((Finset.univ.filter (fun x : ZMod p => x * x = t)).card : ℂ) *
          (ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro t _
        have hin : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x * x = t),
            ρ (x * x) * ((quadraticChar (ZMod p) (x * x + a) : ℤ) : ℂ) =
              ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) := by
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t : ZMod p, (ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) +
          ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hfib t, ← hρ t]
        ring
    _ = ∑ t : ZMod p, ρ t * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) +
        ∑ t : ZMod p, ρ t ^ 3 * ((quadraticChar (ZMod p) (t + a) : ℤ) : ℂ) :=
        Finset.sum_add_distrib

end MPP.Solutions.Bsd259
