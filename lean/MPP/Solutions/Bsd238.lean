import Mathlib

namespace MPP.Solutions.Bsd238

theorem tower_count (G : Type) [AddCommGroup G] (ℓ e : ℕ) (hsurj : ∀ x : G, ∃ y : G, ℓ • y = x) :
    Nat.card {x : G // (ℓ ^ (e + 1)) • x = 0} = Nat.card {x : G // ℓ • x = 0} * Nat.card {x : G // ℓ ^ e • x = 0} := by
  have hπ : ∀ x : G, (ℓ ^ (e + 1)) • x = 0 → ℓ ^ e • (ℓ • x) = 0 := by
    intro x hx
    rw [← mul_smul, ← pow_succ]
    exact hx
  obtain ⟨π, hπdef⟩ : ∃ π : {x : G // (ℓ ^ (e + 1)) • x = 0} → {x : G // ℓ ^ e • x = 0},
      ∀ x, (π x).1 = ℓ • x.1 :=
    ⟨fun x => ⟨ℓ • x.1, hπ x.1 x.2⟩, fun x => rfl⟩
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨x0, hx0⟩ := hsurj y
    refine ⟨⟨x0, ?_⟩, Subtype.ext ?_⟩
    · rw [pow_succ, mul_smul, hx0]
      exact hy
    · rw [hπdef]
      exact hx0
  choose s hs using hπs
  have hsy : ∀ y, ℓ • (s y).1 = y.1 := fun y => by
    rw [← hπdef, hs y]
  have hfmem : ∀ (y : {x : G // ℓ ^ e • x = 0}) (z : {x : G // ℓ • x = 0}),
      (ℓ ^ (e + 1)) • ((s y).1 + z.1) = 0 := by
    intro y z
    rw [smul_add, (s y).2, zero_add, pow_succ, mul_smul, z.2, smul_zero]
  obtain ⟨f, hfdef⟩ : ∃ f : {x : G // ℓ ^ e • x = 0} × {x : G // ℓ • x = 0} →
      {x : G // (ℓ ^ (e + 1)) • x = 0}, ∀ p, (f p).1 = (s p.1).1 + p.2.1 :=
    ⟨fun p => ⟨(s p.1).1 + p.2.1, hfmem p.1 p.2⟩, fun p => rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hh : (s y).1 + z.1 = (s y').1 + z'.1 := by
      have := congrArg Subtype.val h
      rw [hfdef, hfdef] at this
      exact this
    have e1 : ℓ • ((s y).1 + z.1) = y.1 := by rw [smul_add, hsy y, z.2, add_zero]
    have e2 : ℓ • ((s y').1 + z'.1) = y'.1 := by rw [smul_add, hsy y', z'.2, add_zero]
    have hyy : y = y' := Subtype.ext (by rw [← e1, ← e2, hh])
    subst hyy
    have hzz : z = z' := Subtype.ext (add_left_cancel hh)
    subst hzz
    rfl
  have hsurj' : Function.Surjective f := by
    intro x
    refine ⟨(π x, ⟨x.1 - (s (π x)).1, ?_⟩), Subtype.ext ?_⟩
    · rw [smul_sub, hsy (π x), ← hπdef]
      exact sub_self _
    · rw [hfdef]
      show (s (π x)).1 + (x.1 - (s (π x)).1) = x.1
      abel
  have hbij : Function.Bijective f := ⟨hinj, hsurj'⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, mul_comm]

theorem main : ∀ (G : Type) [AddCommGroup G] (ℓ : ℕ), (∀ x : G, ∃ y : G, ℓ • y = x) →
    ℓ ^ 2 ≤ Nat.card {x : G // ℓ • x = 0} → ∀ e : ℕ, (ℓ ^ e) ^ 2 ≤ Nat.card {x : G // (ℓ ^ e) • x = 0} := by
  intro G _ ℓ hsurj hℓ e
  induction e with
  | zero =>
    rw [pow_zero, one_pow]
    have hsub : Subsingleton {x : G // 1 • x = 0} := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : G) = 0 := by
        have h := a.2
        rwa [one_smul] at h
      have hb : (b : G) = 0 := by
        have h := b.2
        rwa [one_smul] at h
      rw [ha, hb]
    haveI := hsub
    haveI : Nonempty {x : G // 1 • x = 0} := ⟨⟨0, by simp⟩⟩
    exact Nat.card_pos
  | succ n ih =>
    rw [tower_count G ℓ n hsurj]
    calc (ℓ ^ (n + 1)) ^ 2 = ℓ ^ 2 * (ℓ ^ n) ^ 2 := by ring
      _ ≤ Nat.card {x : G // ℓ • x = 0} * Nat.card {x : G // ℓ ^ n • x = 0} := Nat.mul_le_mul hℓ ih

end MPP.Solutions.Bsd238
