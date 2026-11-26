import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp032
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp120
import MPP.Solutions.Pnp125
import MPP.Solutions.Pnp242

namespace MPP.Solutions.Pnp243

open MPP.PvsNP Turing

theorem main : ∃ Q : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) Q) ∧
    ∀ u v : List Bool, v ≠ [] → Q (pair u v) = List.replicate (u.length / v.length) true := by
  obtain ⟨d, ⟨hd⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, he_eq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨g, ⟨hg⟩, hg_eq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨M, ⟨hM⟩, hM_eq⟩ := MPP.Solutions.Pnp032.main
  obtain ⟨C, hCin, hC_eq⟩ := MPP.Solutions.Pnp028.main
  have hCval : ∀ x w : List Bool, C (pair x w) = decide (w.length ≤ x.length) := by
    intro x w
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hC_eq x w
  -- A z = replicate (|e z| + 1) false
  have hge : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => g (e z))) :=
    MPP.Solutions.Pnp006.main he hg
  obtain ⟨A, ⟨hA⟩, hA_eq⟩ := MPP.Solutions.Pnp125.main (fun z => g (e z)) false hge
  have hA' : ∀ z, A z = List.replicate ((e z).length + 1) false := by
    intro z
    rw [hA_eq z]
    simp [hg_eq, List.replicate_succ']
  -- P1 z = pair (A z) (e (d z)), and W z = M (P1 z) = replicate ((|e z| + 1) * |v|) false
  have hV : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => e (d z))) :=
    MPP.Solutions.Pnp006.main hd he
  obtain ⟨P1, ⟨hP1⟩, hP1_eq⟩ := MPP.Solutions.Pnp026.main A (fun z => e (d z)) ⟨hA⟩ hV
  have hW : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => M (P1 z))) :=
    MPP.Solutions.Pnp006.main hP1 hM
  -- B z = replicate (|d (d z)| + 1) false
  obtain ⟨hdd0⟩ := MPP.Solutions.Pnp006.main hd hd
  obtain ⟨B, ⟨hB⟩, hB_eq⟩ := MPP.Solutions.Pnp125.main (fun z => g (d (d z))) false
    (MPP.Solutions.Pnp006.main hdd0 hg)
  have hB' : ∀ z, B z = List.replicate ((d (d z)).length + 1) false := by
    intro z
    rw [hB_eq z]
    simp [hg_eq, List.replicate_succ']
  -- P2 z = pair (W z) (B z), and C (P2 z) says |B z| ≤ |W z|, i.e. |v|·(k+1) ≥ |u| + 1
  obtain ⟨P2, ⟨hP2⟩, hP2_eq⟩ :=
    MPP.Solutions.Pnp026.main (fun z => M (P1 z)) B hW ⟨hB⟩
  -- the language D z = C (P2 z) is in P, and Pnp060 appends !D z
  have hD : InP (fun z => C (P2 z)) := MPP.Solutions.Pnp008.main C P2 hCin hP2
  obtain ⟨s, ⟨hs⟩, hs_eq⟩ := MPP.Solutions.Pnp060.main _ hD
  -- G z = pair (s z) (replicate |z| false), and Dr drops |z| symbols: c z = [!C (P2 z)]
  have hG : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => s z)) := ⟨hs⟩
  obtain ⟨G, ⟨hGt⟩, hG_eq⟩ := MPP.Solutions.Pnp026.main s g ⟨hs⟩ ⟨hg⟩
  obtain ⟨Dr, ⟨hDr⟩, hDr_eq⟩ := MPP.Solutions.Pnp120.main
  have hc : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => Dr (G z))) :=
    MPP.Solutions.Pnp006.main hGt hDr
  have hc_eq : ∀ z, Dr (G z) = [!(C (P2 z))] := by
    intro z
    rw [hG_eq z, hDr_eq, hg_eq, hs_eq]
    simp [List.drop_left']
  -- the bit, in the form needed for the count
  have hbit : ∀ u v : List Bool, ∀ k : ℕ,
      (!(C (P2 (pair (pair u v) (List.replicate k false))))) =
        decide ((k + 1) * v.length ≤ u.length) := by
    intro u v k
    have hz_d : d (pair (pair u v) (List.replicate k false)) = pair u v := hd_eq _ _
    have hz_e : e (pair (pair u v) (List.replicate k false)) = List.replicate k false := he_eq _ _
    have hv : e (d (pair (pair u v) (List.replicate k false))) = v := by
      rw [hz_d, he_eq]
    have hu : d (d (pair (pair u v) (List.replicate k false))) = u := by
      rw [hz_d, hd_eq]
    rw [hP2_eq, hCval]
    simp only [hP1_eq, hA', hz_e, hv, hB', hu, hM_eq]
    by_cases h : (k + 1) * v.length ≤ u.length
    · simp [h]
    · simp [h]
      omega

  obtain ⟨q, ⟨hq⟩, hq_eq⟩ := MPP.Solutions.Pnp242.main (fun z => Dr (G z)) hc
  refine ⟨q, ⟨hq⟩, ?_⟩
  intro u v hv
  have hpos : 0 < v.length := List.length_pos_iff.mpr hv
  have hcnt : ∀ N n : ℕ, (List.range N).countP (fun k => decide (k < n)) = min N n := by
    intro N n
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.countP_append, ih]
      by_cases h : N < n
      · simp [h, min_def]
        omega
      · simp [h, min_def]
        omega
  have hdiv : ∀ k : ℕ, decide ((k + 1) * v.length ≤ u.length) = decide (k < u.length / v.length) := by
    intro k
    congr 1
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hpos]
  have hlen : u.length / v.length ≤ (pair u v).length + 1 := by
    have h1 : u.length / v.length ≤ u.length := Nat.div_le_self _ _
    have h2 : u.length ≤ (pair u v).length := by
      unfold pair
      simp
      omega
    omega
  rw [hq_eq]
  congr 1
  simp only [hc_eq, List.headD_cons, hbit, hdiv]
  rw [hcnt, Nat.min_eq_right hlen]

end MPP.Solutions.Pnp243
