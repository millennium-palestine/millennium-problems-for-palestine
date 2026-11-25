import Mathlib

namespace MPP.Solutions.Bsd233

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (a b c d : K), a ≠ 0 →
    b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d ≠ 0 →
    3 ≤ Nat.card {x : K // a * x ^ 3 + b * x ^ 2 + c * x + d = 0} := by
  intro K _ _ a b c d ha hd
  classical
  let P : Cubic K := ⟨a, b, c, d⟩
  have hdisc : P.discr ≠ 0 := hd
  have hsplit : (P.toPoly.map (RingHom.id K)).Splits := IsAlgClosed.splits _
  have hcard := Cubic.card_roots_of_discr_ne_zero (φ := RingHom.id K) ha hsplit hdisc
  have hpoly : P.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
  have hroots : ∀ x : K, x ∈ (Cubic.map (RingHom.id K) P).roots ↔
      a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
    intro x
    rw [Cubic.map_roots, Polynomial.map_id, Polynomial.mem_roots]
    · simp [Polynomial.IsRoot.def, Cubic.toPoly, P]
    · simpa using hpoly
  have hS := Polynomial.finite_setOf_isRoot hpoly
  haveI := hS.to_subtype
  haveI : Finite {x : K // a * x ^ 3 + b * x ^ 2 + c * x + d = 0} :=
    Finite.of_injective
      (fun x : {x : K // a * x ^ 3 + b * x ^ 2 + c * x + d = 0} =>
        (⟨x.1, by simp [Polynomial.IsRoot.def, Cubic.toPoly, P]⟩ :
          {x : K | P.toPoly.IsRoot x}))
      (fun x y h => Subtype.ext (Subtype.mk.inj h))
  calc 3 = (Cubic.map (RingHom.id K) P).roots.toFinset.card := hcard.symm
    _ = Nat.card ((Cubic.map (RingHom.id K) P).roots.toFinset) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card {x : K // a * x ^ 3 + b * x ^ 2 + c * x + d = 0} :=
      Nat.card_le_card_of_injective
        (fun y => ⟨y.1, (hroots y.1).mp (Multiset.mem_toFinset.mp y.2)⟩)
        (fun y z h => Subtype.ext (Subtype.mk.inj h))

end MPP.Solutions.Bsd233
