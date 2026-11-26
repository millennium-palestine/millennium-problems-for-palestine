import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp032
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp237
import MPP.Solutions.Pnp242
import MPP.Solutions.Pnp243

namespace MPP.Solutions.Pnp244

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

theorem main : ∃ R : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) R) ∧
    ∀ u v : List Bool, v ≠ [] → R (pair u v) = List.replicate (u.length % v.length) true := by
  obtain ⟨d, hd, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, he, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨C, hCP, hCeq⟩ := MPP.Solutions.Pnp028.main
  obtain ⟨g, hg, hgeq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨one, hone, honeq⟩ := MPP.Solutions.Pnp030.main 1
  obtain ⟨M, hM, hMeq⟩ := MPP.Solutions.Pnp032.main
  obtain ⟨Q, hQ, hQeq⟩ := MPP.Solutions.Pnp243.main
  -- the product |v| * (|u| / |v|), as a unary string, from the first component and the quotient
  obtain ⟨P1, hP1, hP1eq⟩ := MPP.Solutions.Pnp237.pairP
    (MPP.Solutions.Pnp237.comp (MPP.Solutions.Pnp237.comp hd he) hg)
    (MPP.Solutions.Pnp237.comp hd hQ)
  have hF : MPP.Solutions.Pnp237.PT (M ∘ P1) := MPP.Solutions.Pnp237.comp hP1 hM
  -- the bit A: |v| * (|u| / |v|) at most k, the length of the witness part
  obtain ⟨P2, hP2, hP2eq⟩ := MPP.Solutions.Pnp237.pairP he hF
  have hA : InP (fun z => C (P2 z)) := MPP.Solutions.Pnp237.langComp hCP hP2
  -- the bit B: k + 1 at most |u|, from the witness part extended by one false
  obtain ⟨E1, hE1, hE1eq⟩ := MPP.Solutions.Pnp127.main e one he hone
  obtain ⟨P3, hP3, hP3eq⟩ := MPP.Solutions.Pnp237.pairP (MPP.Solutions.Pnp237.comp hd hd) hE1
  have hB : InP (fun z => C (P3 z)) := MPP.Solutions.Pnp237.langComp hCP hP3
  have hAB : InP (fun z => C (P2 z) && C (P3 z)) := MPP.Solutions.Pnp011.main _ _ hA hB
  obtain ⟨H, hH, hHeq⟩ := MPP.Solutions.Pnp237.langMap _ hAB
  obtain ⟨R, hR, hReq⟩ := MPP.Solutions.Pnp242.main H hH
  refine ⟨R, hR, fun u v hv => ?_⟩
  have hbit : ∀ k : ℕ, (H (pair (pair u v) (List.replicate k false))).headD false =
      decide (v.length * (u.length / v.length) ≤ k ∧ k < u.length) := by
    intro k
    set z := pair (pair u v) (List.replicate k false) with hz
    have hdz : d z = pair u v := hdeq _ _
    have hez : e z = List.replicate k false := heeq _ _
    have hddz : d (d z) = u := by rw [hdz, hdeq]
    have hF1 : (M ∘ P1) z = List.replicate (v.length * (u.length / v.length)) false := by
      simp only [Function.comp_apply, hP1eq, hMeq, hdz, heeq, hgeq, hQeq u v hv,
        List.length_replicate]
    have hC2 : C (P2 z) = true ↔ v.length * (u.length / v.length) ≤ k := by
      rw [hP2eq, hez, hF1, hCeq, List.length_replicate, List.length_replicate]
    have hC3 : C (P3 z) = true ↔ k < u.length := by
      rw [hP3eq, Function.comp_apply, hddz, hCeq, hE1eq, hez, List.length_append,
        List.length_replicate, honeq, List.length_replicate]
      omega
    have hC2' : C (P2 z) = decide (v.length * (u.length / v.length) ≤ k) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, hC2]
    have hC3' : C (P3 z) = decide (k < u.length) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, hC3]
    simp only [hHeq, List.headD_cons, hC2', hC3', Bool.decide_and]
  rw [hReq (pair u v)]
  congr 1
  simp only [hbit]
  rw [aux_count_band, aux_length]
  have hdm := Nat.div_add_mod u.length v.length
  generalize v.length * (u.length / v.length) = P at hdm ⊢
  generalize u.length % v.length = r at hdm ⊢
  omega

end MPP.Solutions.Pnp244
