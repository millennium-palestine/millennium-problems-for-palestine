import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp038
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp066
import MPP.Solutions.Pnp081
import MPP.Solutions.Pnp118
import MPP.Solutions.Pnp120
import MPP.Solutions.Pnp122
import MPP.Solutions.Pnp125
import MPP.Solutions.Pnp127

namespace MPP.Solutions.Pnp229

open MPP.PvsNP Turing

theorem main : ∀ h : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) h) →
    ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool,
        f x = [(List.range (x.length + 1)).any (fun m => (h (pair x (List.replicate m true))).headD false)] := by
  intro h hh
  obtain ⟨d, ⟨hd⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, he_eq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨u, ⟨hu⟩, hu_eq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨r, ⟨hr⟩, hr_eq⟩ := MPP.Solutions.Pnp081.main
  have hid : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (id : List Bool → List Bool)) :=
    MPP.Solutions.Pnp037.main
  have hpx : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun x : List Bool => pair x [])) :=
    MPP.Solutions.Pnp038.main
  -- P z = pair (d z) (unary false of |e z|), and r turns it into the unary true
  have hue : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => u (e z))) :=
    MPP.Solutions.Pnp006.main he hu
  obtain ⟨P, ⟨hP⟩, hP_eq⟩ := MPP.Solutions.Pnp026.main d (fun z => u (e z)) ⟨hd⟩ hue
  have hA : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => r (P z))) :=
    MPP.Solutions.Pnp006.main hP hr
  have hA_eq : ∀ z, r (P z) = pair (d z) (List.replicate (e z).length true) := by
    intro z
    rw [hP_eq z]
    show r (pair (d z) (u (e z))) = _
    rw [hr_eq, hu_eq, List.map_replicate]
    rfl
  obtain ⟨hA'⟩ := hA
  obtain ⟨hh'⟩ := hh
  have hHA := MPP.Solutions.Pnp006.main hA' hh'
  obtain ⟨hHA'⟩ := hHA
  -- the bit is the head of h (A z), with a false appended and then cut to one symbol
  obtain ⟨Q, ⟨hQ⟩, hQ_eq⟩ := MPP.Solutions.Pnp125.main _ false ⟨hHA'⟩
  obtain ⟨Tk, ⟨hTk⟩, hTk_eq⟩ := MPP.Solutions.Pnp118.main 1
  have hbl := MPP.Solutions.Pnp006.main hQ hTk
  obtain ⟨hbl'⟩ := hbl
  have htake : ∀ L : List Bool, (L ++ [false]).take 1 = [L.headD false] := by
    intro L
    cases L <;> simp
  have hbit : ∀ z, Tk (Q z) = [(h (r (P z))).headD false] := by
    intro z
    rw [hTk_eq, hQ_eq]
    exact htake _
  -- the step: append one bit computed from the instance and the current witness
  obtain ⟨S, ⟨hS⟩, hS_eq⟩ :=
    MPP.Solutions.Pnp127.main id (fun z => Tk (Q z)) hid ⟨hbl'⟩
  have hS_len : ∀ z, (S z).length = z.length + 1 := by
    intro z
    rw [hS_eq z]
    simp [hbit]
  have hstep : ∀ x B : List Bool,
      S (pair x B) = pair x (B ++ [(h (pair x (List.replicate B.length true))).headD false]) := by
    intro x B
    rw [hS_eq]
    simp only [id_eq]
    rw [hbit]
    have hk : r (P (pair x B)) = pair x (List.replicate B.length true) := by
      rw [hA_eq, hd_eq, he_eq]
    rw [hk]
    simp only [pair, List.append_assoc]
  have hiter : ∀ x : List Bool, ∀ k : ℕ, S^[k] (pair x []) =
      pair x ((List.range k).map (fun m => (h (pair x (List.replicate m true))).headD false)) := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hstep]
      congr 1
      simp [List.range_succ]
  -- the iteration count |x| + 1 comes from a unary witness of that length
  obtain ⟨T, ⟨hT⟩, hT_eq⟩ := MPP.Solutions.Pnp066.main S ⟨hS⟩ hS_len
  obtain ⟨g', ⟨hg'⟩, hg'_eq⟩ := MPP.Solutions.Pnp125.main u false ⟨hu⟩
  obtain ⟨P0, ⟨hP0⟩, hP0_eq⟩ :=
    MPP.Solutions.Pnp026.main (fun x => pair x []) g' hpx ⟨hg'⟩
  have hP0x : ∀ x : List Bool, P0 x = pair (pair x []) (List.replicate (x.length + 1) false) := by
    intro x
    rw [hP0_eq x]
    show pair (pair x []) (g' x) = _
    rw [hg'_eq x, hu_eq x, List.replicate_succ']
  -- the final decision: the OR of the bits is the negated all-false test of the witness
  have hD_in : InP (fun z => decide (∀ b ∈ e (r z), b = true)) := by
    have hre := MPP.Solutions.Pnp006.main hr he
    obtain ⟨hre'⟩ := hre
    exact MPP.Solutions.Pnp008.main _ (fun z => e (r z)) MPP.Solutions.Pnp122.main hre'
  obtain ⟨s2, ⟨hs2⟩, hs2_eq⟩ := MPP.Solutions.Pnp060.main _ hD_in
  obtain ⟨P2, ⟨hP2⟩, hP2_eq⟩ := MPP.Solutions.Pnp026.main s2 id ⟨hs2⟩ hid
  obtain ⟨Dr, ⟨hDr⟩, hDr_eq⟩ := MPP.Solutions.Pnp120.main
  have hF := MPP.Solutions.Pnp006.main hP2 hDr
  obtain ⟨hF'⟩ := hF
  have hTP := MPP.Solutions.Pnp006.main hP0 hT
  obtain ⟨hTP'⟩ := hTP
  have hfin := MPP.Solutions.Pnp006.main hTP' hF'
  have key : ∀ B : List Bool, (!decide (∀ b ∈ B.map (fun b => !b), b = true)) = B.any id := by
    intro B
    induction B with
    | nil => rfl
    | cons a t ih => cases a <;> simp_all
  refine ⟨_, hfin, ?_⟩
  intro x
  show Dr (P2 (T (P0 x))) = _
  rw [hP0x, hT_eq, hiter, hP2_eq, hDr_eq, hs2_eq]
  simp only [id_eq]
  rw [List.drop_left' rfl]
  simp only [hr_eq, he_eq]
  congr 1
  rw [key, List.any_map]
  rfl

end MPP.Solutions.Pnp229
