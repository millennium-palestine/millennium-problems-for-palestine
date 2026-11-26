import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp237
import MPP.Solutions.Pnp242

namespace MPP.Solutions.Pnp245

open MPP.PvsNP Turing

theorem aux_count_band (a b N : ℕ) :
    (List.range N).countP (fun k => decide (a ≤ k ∧ k < b)) = min N b - min N a := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h1 : a ≤ N <;> by_cases h2 : N < b <;> simp [h1, h2] <;> omega

theorem aux_length (u v : List Bool) : (pair u v).length = 2 * u.length + 2 + v.length := by
  have hf : ∀ y : List Bool, (y.flatMap fun b => [b, b]).length = 2 * y.length := by
    intro y
    induction y with
    | nil => simp
    | cons a t ih => simp [ih] <;> omega
  simp only [pair, List.length_append, hf]
  simp

theorem main : ∃ S : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) S) ∧
    ∀ u v : List Bool, S (pair u v) = List.replicate (u.length - v.length) true := by
  obtain ⟨d, hd, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, he, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨C, hCP, hCeq⟩ := MPP.Solutions.Pnp028.main
  obtain ⟨one, hone, honeq⟩ := MPP.Solutions.Pnp030.main 1
  obtain ⟨E1, hE1, hE1eq⟩ := MPP.Solutions.Pnp127.main e one he hone
  obtain ⟨f1, hf1, hf1eq⟩ := MPP.Solutions.Pnp237.pairP he (MPP.Solutions.Pnp237.comp hd he)
  have hdd := MPP.Solutions.Pnp237.comp hd hd
  obtain ⟨f2, hf2, hf2eq⟩ := MPP.Solutions.Pnp237.pairP hdd hE1
  have hP1 : InP (fun z => C (f1 z)) := MPP.Solutions.Pnp237.langComp hCP hf1
  have hP2 : InP (fun z => C (f2 z)) := MPP.Solutions.Pnp237.langComp hCP hf2
  have hP := MPP.Solutions.Pnp011.main _ _ hP1 hP2
  obtain ⟨h, hh, hheq⟩ := MPP.Solutions.Pnp237.langMap _ hP
  obtain ⟨Q, hQ, hQeq⟩ := MPP.Solutions.Pnp242.main h hh
  refine ⟨Q, hQ, fun u v => ?_⟩
  have hl := aux_length u v
  have h1 : ∀ k : ℕ, f1 (pair (pair u v) (List.replicate k false)) =
      pair (List.replicate k false) v := by
    intro k
    rw [hf1eq]
    simp [heeq, hdeq, Function.comp_apply]
  have h2 : ∀ k : ℕ, f2 (pair (pair u v) (List.replicate k false)) =
      pair u (List.replicate k false ++ List.replicate 1 false) := by
    intro k
    rw [hf2eq]
    simp [hdeq, heeq, hE1eq, honeq, Function.comp_apply]
  have hbit : ∀ k : ℕ, (h (pair (pair u v) (List.replicate k false))).headD false =
      decide (v.length ≤ k ∧ k < u.length) := by
    intro k
    have hc1 : C (pair (List.replicate k false) v) = decide (v.length ≤ k) := by
      rw [Bool.eq_iff_iff, hCeq]
      simp
    have hc2 : C (pair u (List.replicate k false ++ List.replicate 1 false)) = decide (k < u.length) := by
      rw [Bool.eq_iff_iff, hCeq]
      simp only [List.length_append, List.length_replicate, decide_eq_true_iff]
      constructor <;> intro hh <;> omega
    rw [hheq]
    simp only [List.headD_cons]
    rw [h1 k, h2 k, hc1, hc2, ← Bool.decide_and]
  have hdiv : u.length ≤ (pair u v).length + 1 := by omega
  have hsub : v.length ≤ (pair u v).length + 1 := by omega
  rw [hQeq]
  congr 1
  simp only [hbit]
  rw [aux_count_band, Nat.min_eq_right hdiv, Nat.min_eq_right hsub]

end MPP.Solutions.Pnp245
