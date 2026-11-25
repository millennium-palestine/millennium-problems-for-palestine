import Mathlib
import MPP.Solutions.Bsd229

namespace MPP.Solutions.Bsd230

theorem main : ∀ (G : Type) [AddCommGroup G] (m : ℕ), 0 < m →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → Nat.card {x : G // ℓ • x = 0} ≤ ℓ ^ 2) →
    Nat.card {x : G // m • x = 0} ≤ m ^ 2 := by
  intro G _ m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hp
    by_cases h1 : m = 1
    · subst h1
      have hz : ∀ a : {x : G // 1 • x = 0}, a.1 = 0 := fun a => by
        have ha := a.2
        rwa [one_nsmul] at ha
      have hcard : Nat.card {x : G // 1 • x = 0} = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ((hz a).trans (hz b).symm)⟩, ⟨⟨0, by simp⟩⟩⟩
      rw [hcard]
      norm_num
    · obtain ⟨ℓ, hℓ, k, rfl⟩ := Nat.exists_prime_and_dvd h1
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          simp at hm
        · exact h
      have hlt : k < ℓ * k := by
        have h2 := hℓ.two_le
        nlinarith
      have hA : Nat.card {x : G // ℓ • x = 0} ≤ ℓ ^ 2 := hp ℓ hℓ (dvd_mul_right ℓ k)
      have hB : Nat.card {x : G // k • x = 0} ≤ k ^ 2 :=
        ih k hlt hk0 (fun q hq hqk => hp q hq (dvd_mul_of_dvd_right hqk ℓ))
      calc Nat.card {x : G // (ℓ * k) • x = 0}
          ≤ Nat.card {x : G // ℓ • x = 0} * Nat.card {x : G // k • x = 0} :=
            MPP.Solutions.Bsd229.main G ℓ k
        _ ≤ ℓ ^ 2 * k ^ 2 := Nat.mul_le_mul hA hB
        _ = (ℓ * k) ^ 2 := by ring

end MPP.Solutions.Bsd230
