import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp038
import MPP.Solutions.Pnp066
import MPP.Solutions.Pnp094
import MPP.Solutions.Pnp118
import MPP.Solutions.Pnp125
import MPP.Solutions.Pnp127

namespace MPP.Solutions.Pnp242

open MPP.PvsNP Turing

theorem main : ∀ c : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) c) →
    ∃ q : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) q) ∧
      ∀ x : List Bool, q x = List.replicate ((List.range (x.length + 1)).countP
        (fun k => (c (pair x (List.replicate k false))).headD false)) true := by
  intro c hc
  obtain ⟨d, ⟨hd⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, he_eq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨u, ⟨hu⟩, hu_eq⟩ := MPP.Solutions.Pnp029.main
  have hid : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (id : List Bool → List Bool)) :=
    MPP.Solutions.Pnp037.main
  have hpx : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun x : List Bool => pair x [])) :=
    MPP.Solutions.Pnp038.main
  -- P z = pair (d z) (unary false of |e z|), so P (pair x B) = pair x (replicate |B| false)
  have hue : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => u (e z))) :=
    MPP.Solutions.Pnp006.main he hu
  obtain ⟨P, ⟨hP⟩, hP_eq⟩ := MPP.Solutions.Pnp026.main d (fun z => u (e z)) ⟨hd⟩ hue
  have hP' : ∀ z : List Bool, P z = pair (d z) (List.replicate (e z).length false) := by
    intro z
    rw [hP_eq z, hu_eq]
  obtain ⟨hc'⟩ := hc
  obtain ⟨hA⟩ := MPP.Solutions.Pnp006.main hP hc'
  -- the bit is the head of c (P z), with a false appended and then cut to one symbol
  obtain ⟨Q, ⟨hQ⟩, hQ_eq⟩ := MPP.Solutions.Pnp125.main _ false ⟨hA⟩
  obtain ⟨Tk, ⟨hTk⟩, hTk_eq⟩ := MPP.Solutions.Pnp118.main 1
  have hbl := MPP.Solutions.Pnp006.main hQ hTk
  obtain ⟨hbl'⟩ := hbl
  have htake : ∀ L : List Bool, (L ++ [false]).take 1 = [L.headD false] := by
    intro L
    cases L <;> simp
  have hbit : ∀ z, Tk (Q z) = [(c (P z)).headD false] := by
    intro z
    rw [hTk_eq, hQ_eq]
    exact htake _
  -- the step appends one bit to the witness: z ↦ z ++ bit(z)
  obtain ⟨S, ⟨hS⟩, hS_eq⟩ :=
    MPP.Solutions.Pnp127.main id (fun z => Tk (Q z)) hid ⟨hbl'⟩
  have hS_len : ∀ z, (S z).length = z.length + 1 := by
    intro z
    rw [hS_eq z]
    simp [hbit]
  have hstep : ∀ x B : List Bool,
      S (pair x B) = pair x (B ++ [(c (pair x (List.replicate B.length false))).headD false]) := by
    intro x B
    rw [hS_eq]
    simp only [id_eq]
    rw [hbit]
    have hk : P (pair x B) = pair x (List.replicate B.length false) := by
      rw [hP', hd_eq, he_eq]
    rw [hk]
    simp only [pair, List.append_assoc]
  have hiter : ∀ x : List Bool, ∀ k : ℕ, S^[k] (pair x []) =
      pair x ((List.range k).map (fun m => (c (pair x (List.replicate m false))).headD false)) := by
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
  -- the final answer: the unary count of true bits of the witness after |x| + 1 steps
  obtain ⟨Cn, ⟨hCn⟩, hCn_eq⟩ := MPP.Solutions.Pnp094.main
  have hTP := MPP.Solutions.Pnp006.main hP0 hT
  obtain ⟨hTP'⟩ := hTP
  have hfin := MPP.Solutions.Pnp006.main hTP' hCn
  refine ⟨_, hfin, ?_⟩
  intro x
  show Cn (T (P0 x)) = _
  rw [hP0x, hT_eq, hiter, hCn_eq]
  congr 1
  simp [List.count_eq_countP, List.countP_map]
  rfl

end MPP.Solutions.Pnp242
