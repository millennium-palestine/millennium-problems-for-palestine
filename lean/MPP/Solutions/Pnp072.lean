import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp033
import MPP.Solutions.Pnp038
import MPP.Solutions.Pnp056
import MPP.Solutions.Pnp058
import MPP.Solutions.Pnp059
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp066
import MPP.Solutions.Pnp070
import MPP.Solutions.Pnp071

namespace MPP.Solutions.Pnp072

open MPP.PvsNP Turing

/-- Appending a bit to the pair encoding appends it to the second component. -/
theorem pair_append_bit (x u : List Bool) (b : Bool) :
    pair x u ++ [b] = pair x (u ++ [b]) := by
  unfold pair
  simp [List.append_assoc]

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V → PEqualsNP →
    ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
        (f x).length = p.eval x.length ∧ V (pair x (f x)) = true ∧
        ∀ w : List Bool, w.length = p.eval x.length → V (pair x w) = true → ¬ (w < f x) := by
  intro V p hV hPNP
  classical
  obtain ⟨D, hD, hDx⟩ := MPP.Solutions.Pnp070.main V p hV hPNP
  obtain ⟨s, ⟨hs⟩, hsx⟩ := MPP.Solutions.Pnp056.main
  obtain ⟨G, ⟨hG⟩, hGz⟩ :=
    MPP.Solutions.Pnp060.main (fun y => D (s y)) (MPP.Solutions.Pnp008.main D s hD hs)
  -- the one-bit step on pairs, and its length
  have hGpair : ∀ x u, G (pair x u) = pair x (u ++ [!D (pair x (u ++ [false]))]) := by
    intro x u
    have h := hGz (pair x u)
    simp only [hsx] at h
    rw [h, pair_append_bit]
  have hGlen : ∀ z, (G z).length = z.length + 1 := by
    intro z
    rw [hGz z]
    simp
  obtain ⟨T, ⟨hT⟩, hTz⟩ := MPP.Solutions.Pnp066.main G ⟨hG⟩ hGlen
  -- the fixed-length count and the pair with the empty witness
  obtain ⟨g, ⟨hg⟩, hgx⟩ := MPP.Solutions.Pnp033.main p
  obtain ⟨h, ⟨hh⟩, hhx⟩ :=
    MPP.Solutions.Pnp026.main (fun x => pair x []) g MPP.Solutions.Pnp038.main ⟨hg⟩
  obtain ⟨hTh⟩ := MPP.Solutions.Pnp006.main hh hT
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨hf⟩ := MPP.Solutions.Pnp006.main hTh he
  refine ⟨e ∘ (T ∘ h), ⟨hf⟩, fun x hw => ?_⟩
  -- the greedy step: the bit is 1 exactly when no extension by false is accepted
  obtain ⟨step, hstep⟩ : ∃ step : List Bool → List Bool, ∀ u : List Bool,
      step u = if D (pair x (u ++ [false])) = true then u ++ [false] else u ++ [true] :=
    ⟨_, fun u => rfl⟩
  have hGstep : ∀ u, G (pair x u) = pair x (step u) := by
    intro u
    rw [hGpair x u, hstep u]
    generalize D (pair x (u ++ [false])) = b
    cases b <;> simp
  have key : ∀ k : ℕ, G^[k] (pair x []) = pair x (step^[k] []) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hGstep]
  -- the greedy invariant, from pnp-059 and pnp-058
  have hiff : ∀ u : List Bool, D (pair x u) = true ↔
      ∃ w : List Bool, w.length = p.eval x.length ∧ (∃ t : List Bool, w = u ++ t) ∧
        V (pair x w) = true := by
    intro u
    rw [hDx x u]
    constructor
    · rintro ⟨t, ht, hv⟩
      exact ⟨u ++ t, ht, ⟨t, rfl⟩, hv⟩
    · rintro ⟨w, hw, ⟨t, rfl⟩, hv⟩
      exact ⟨t, hw, hv⟩
  obtain ⟨h0, hext⟩ := MPP.Solutions.Pnp059.main V x (p.eval x.length) (fun u => D (pair x u)) hiff hw
  obtain ⟨hlen, hEfin⟩ :=
    MPP.Solutions.Pnp058.main (fun u => D (pair x u)) (p.eval x.length) step h0 hext hstep
  have hfx : (e ∘ (T ∘ h)) x = step^[p.eval x.length] [] := by
    simp only [Function.comp_apply, hhx, hgx]
    rw [hTz, key, hex]
  rw [hfx]
  refine ⟨hlen, ?_, ?_⟩
  · obtain ⟨t, ht, hv⟩ := (hDx x (step^[p.eval x.length] [])).1 hEfin
    have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_append] at ht
      omega)
    subst ht0
    simpa using hv
  · -- minimality: the greedy string is least among accepted witnesses, by pnp-071
    intro w hwlen hwA
    exact MPP.Solutions.Pnp071.main (fun w => V (pair x w) = true) (p.eval x.length)
      (fun u => D (pair x u)) step hiff hstep w hwlen hwA

end MPP.Solutions.Pnp072
