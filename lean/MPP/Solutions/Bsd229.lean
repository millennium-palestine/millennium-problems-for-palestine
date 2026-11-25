import Mathlib

namespace MPP.Solutions.Bsd229

theorem main : ∀ (G : Type) [AddCommGroup G] (ℓ k : ℕ),
    Nat.card {x : G // (ℓ * k) • x = 0} ≤ Nat.card {x : G // ℓ • x = 0} * Nat.card {x : G // k • x = 0} := by
  intro G _ ℓ k
  classical
  have hkℓ : ∀ x : G, k • (ℓ • x) = (ℓ * k) • x := fun x => by
    rw [mul_nsmul]
  have hL : ∀ x : G, ℓ • x = 0 → (ℓ * k) • x = 0 := fun x hx => by
    rw [← hkℓ, hx, nsmul_zero]
  have hK : ∀ x : G, k • x = 0 → (ℓ * k) • x = 0 := fun x hx => by
    rw [mul_comm, mul_nsmul, hx, nsmul_zero]
  by_cases hLf : Finite {x : G // ℓ • x = 0}
  · by_cases hKf : Finite {x : G // k • x = 0}
    · haveI := hLf
      haveI := hKf
      -- the map x ↦ ℓ • x sends the ℓk-torsion into the k-torsion, and the fibres are translates of the ℓ-torsion
      let f : {x : G // (ℓ * k) • x = 0} → {y : G // k • y = 0} :=
        fun x => ⟨ℓ • x.1, by rw [hkℓ]; exact x.2⟩
      haveI : Nonempty {x : G // (ℓ * k) • x = 0} := ⟨⟨0, by simp⟩⟩
      let s : {y : G // k • y = 0} → {x : G // (ℓ * k) • x = 0} := Function.invFun f
      have hs : ∀ x, f (s (f x)) = f x := fun x => Function.invFun_eq ⟨x, rfl⟩
      let g : {x : G // (ℓ * k) • x = 0} → {y : G // k • y = 0} × {z : G // ℓ • z = 0} :=
        fun x => (f x, ⟨x.1 - (s (f x)).1, by
          have h1 : ℓ • (s (f x)).1 = ℓ • x.1 := congrArg Subtype.val (hs x)
          rw [smul_sub, h1, sub_self]⟩)
      have hg : Function.Injective g := by
        intro a b hab
        have hfab : f a = f b := congrArg Prod.fst hab
        have h2 : a.1 - (s (f a)).1 = b.1 - (s (f b)).1 :=
          congrArg (fun z : {y : G // k • y = 0} × {z : G // ℓ • z = 0} => z.2.1) hab
        rw [hfab] at h2
        exact Subtype.ext (sub_left_inj.mp h2)
      have := Nat.card_le_card_of_injective g hg
      rw [Nat.card_prod] at this
      exact this.trans (le_of_eq (mul_comm _ _))
    · haveI : Infinite {x : G // k • x = 0} := not_finite_iff_infinite.mp hKf
      haveI : Infinite {x : G // (ℓ * k) • x = 0} :=
        Infinite.of_injective (fun y : {x : G // k • x = 0} => (⟨y.1, hK y.1 y.2⟩ : {x : G // (ℓ * k) • x = 0}))
          (fun a b h => Subtype.ext (Subtype.mk.inj h))
      rw [Nat.card_eq_zero_of_infinite]
      exact Nat.zero_le _
  · haveI : Infinite {x : G // ℓ • x = 0} := not_finite_iff_infinite.mp hLf
    haveI : Infinite {x : G // (ℓ * k) • x = 0} :=
      Infinite.of_injective (fun y : {x : G // ℓ • x = 0} => (⟨y.1, hL y.1 y.2⟩ : {x : G // (ℓ * k) • x = 0}))
        (fun a b h => Subtype.ext (Subtype.mk.inj h))
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end MPP.Solutions.Bsd229
