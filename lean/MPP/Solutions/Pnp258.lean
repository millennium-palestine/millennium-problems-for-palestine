import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp032
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp125
import MPP.Solutions.Pnp242

namespace MPP.Solutions.Pnp258

open MPP.PvsNP Turing

/-- Counting the k below M + 1 with (k + 1) * n ≤ N gives the quotient N / n. -/
theorem count_div (N n M : ℕ) (hn : 0 < n) (hNM : N ≤ M) :
    (List.range (M + 1)).countP (fun k => decide ((k + 1) * n ≤ N)) = N / n := by
  have hcongr : (List.range (M + 1)).countP (fun k => decide ((k + 1) * n ≤ N))
      = (List.range (M + 1)).countP (fun k => decide (k < N / n)) := by
    apply List.countP_congr
    intro k _
    simp only [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hn]
  have hmin : ∀ m : ℕ, (List.range m).countP (fun k => decide (k < N / n)) = min m (N / n) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.countP_append, ih]
      simp only [List.countP_cons, List.countP_nil]
      split_ifs <;> simp_all <;> omega
  rw [hcongr, hmin]
  have := Nat.div_le_self N n
  omega

theorem main : ∃ Q : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) Q) ∧
    ∀ x w : List Bool, Q (pair x w) = List.replicate (w.length / (x.length + 1)) true := by
  obtain ⟨d, ⟨hd⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, he_eq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨g, ⟨hg⟩, hg_eq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨M, ⟨hM⟩, hM_eq⟩ := MPP.Solutions.Pnp032.main
  obtain ⟨C, hC, hC_eq⟩ := MPP.Solutions.Pnp028.main
  -- on z = pair (pair x w) B: d z = pair x w, d (d z) = x, e (d z) = w, e z = B
  obtain ⟨hdd⟩ := MPP.Solutions.Pnp006.main hd hd
  obtain ⟨hed⟩ := MPP.Solutions.Pnp006.main hd he
  obtain ⟨hge⟩ := MPP.Solutions.Pnp006.main he hg
  obtain ⟨hgdd⟩ := MPP.Solutions.Pnp006.main hdd hg
  -- A z = replicate (|B| + 1) false
  obtain ⟨A, ⟨hA⟩, hA_eq⟩ := MPP.Solutions.Pnp125.main (g ∘ e) false ⟨hge⟩
  -- Bx z = replicate (|x| + 1) false
  obtain ⟨Bx, ⟨hBx⟩, hBx_eq⟩ := MPP.Solutions.Pnp125.main (g ∘ (d ∘ d)) false ⟨hgdd⟩
  -- Hp z = pair (A z) (Bx z), and M (Hp z) = replicate ((|B| + 1) * (|x| + 1)) false
  obtain ⟨Hp, ⟨hHp⟩, hHp_eq⟩ := MPP.Solutions.Pnp026.main A Bx ⟨hA⟩ ⟨hBx⟩
  obtain ⟨hMH⟩ := MPP.Solutions.Pnp006.main hHp hM
  -- F z = pair (e (d z)) (M (Hp z)), the gate's input
  obtain ⟨F, ⟨hF⟩, hF_eq⟩ := MPP.Solutions.Pnp026.main (e ∘ d) (M ∘ Hp) ⟨hed⟩ ⟨hMH⟩
  -- the gate G z = C (F z) is in P, and z ↦ [G z] is a polynomial-time map
  have hG : InP (fun z => C (F z)) := MPP.Solutions.Pnp008.main C F hC hF
  obtain ⟨hN⟩ := MPP.Solutions.Pnp004.main (fun z => C (F z)) hG
  obtain ⟨hW⟩ := MPP.Solutions.Pnp060.negWrapComp
  obtain ⟨hc⟩ := MPP.Solutions.Pnp006.main hN hW
  obtain ⟨Q, ⟨hQ⟩, hQ_eq⟩ := MPP.Solutions.Pnp242.main _ ⟨hc⟩
  refine ⟨Q, ⟨hQ⟩, fun x w => ?_⟩
  -- the gate on the k-th index is the test (k + 1) * (|x| + 1) ≤ |w|
  have hkey : ∀ k : ℕ, C (F (pair (pair x w) (List.replicate k false)))
      = decide ((k + 1) * (x.length + 1) ≤ w.length) := by
    intro k
    have h1 : F (pair (pair x w) (List.replicate k false))
        = pair w (List.replicate ((k + 1) * (x.length + 1)) false) := by
      rw [hF_eq]
      simp [hHp_eq, hA_eq, hBx_eq, hM_eq, hd_eq, he_eq, hg_eq]
    rw [h1]
    have hiff := hC_eq w (List.replicate ((k + 1) * (x.length + 1)) false)
    simp only [List.length_replicate] at hiff
    by_cases hle : (k + 1) * (x.length + 1) ≤ w.length
    · rw [decide_eq_true hle]
      exact hiff.mpr hle
    · rw [decide_eq_false hle]
      cases h : C (pair w (List.replicate ((k + 1) * (x.length + 1)) false)) with
      | false => rfl
      | true => exact absurd (hiff.mp h) hle
  rw [hQ_eq (pair x w)]
  congr 1
  have hNM : w.length ≤ (pair x w).length := by
    simp [MPP.PvsNP.pair]
    omega
  have hcount := count_div w.length (x.length + 1) (pair x w).length (Nat.succ_pos _) hNM
  rw [← hcount]
  congr 1
  funext k
  simp [hkey k]

end MPP.Solutions.Pnp258
