import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp081
import MPP.Solutions.Pnp126
import MPP.Solutions.Pnp227
import MPP.Solutions.Pnp229

namespace MPP.Solutions.Pnp237

open MPP.PvsNP Turing

abbrev PT (f : List Bool → List Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)

theorem comp {f g : List Bool → List Bool} (hf : PT f) (hg : PT g) : PT (g ∘ f) := by
  obtain ⟨hf'⟩ := hf
  obtain ⟨hg'⟩ := hg
  exact MPP.Solutions.Pnp006.main hf' hg'

theorem pairP {f g : List Bool → List Bool} (hf : PT f) (hg : PT g) :
    ∃ h : List Bool → List Bool, PT h ∧ ∀ z, h z = pair (f z) (g z) :=
  MPP.Solutions.Pnp026.main f g hf hg

theorem langComp {L : Lang} {f : List Bool → List Bool} (hL : InP L) (hf : PT f) :
    InP (fun z => L (f z)) := by
  obtain ⟨hf'⟩ := hf
  obtain ⟨hL'⟩ := hL
  exact MPP.Solutions.Pnp006.main hf' hL'

theorem langMap (L : Lang) (hL : InP L) :
    ∃ h : List Bool → List Bool, PT h ∧ ∀ y, h y = [L y] := by
  have hN := MPP.Solutions.Pnp004.main L hL
  obtain ⟨hN'⟩ := hN
  obtain ⟨nw⟩ := MPP.Solutions.Pnp060.negWrapComp
  refine ⟨(fun b : Bool => [!b]) ∘ (fun y => !L y), ?_, fun y => ?_⟩
  · exact MPP.Solutions.Pnp006.main hN' nw
  · simp

theorem unaryTrue : ∃ U : List Bool → List Bool, PT U ∧
    ∀ u : List Bool, U u = List.replicate u.length true := by
  obtain ⟨g, hg, hgeq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨T, hT, hTeq⟩ := MPP.Solutions.Pnp126.main []
  obtain ⟨p, hp, hpeq⟩ := pairP hT hg
  obtain ⟨r, hr, hreq⟩ := MPP.Solutions.Pnp081.main
  obtain ⟨e, he, heeq⟩ := MPP.Solutions.Pnp025.main
  have hrp := comp hp hr
  have hU := comp hrp he
  refine ⟨e ∘ (r ∘ p), hU, fun u => ?_⟩
  simp only [Function.comp_apply, hpeq, hTeq, hreq, heeq, hgeq, List.map_replicate]
  simp

theorem main : ∀ a b : List Bool → List Bool, PT a → PT b →
    ∃ f : List Bool → List Bool, PT f ∧ ∀ x w : List Bool,
      f (pair x w) = [(List.range (x.length + 1)).any (fun m =>
        w.getD (a (pair x (List.replicate m true))).length false &&
          w.getD (b (pair x (List.replicate m true))).length false)] := by
  intro a b ha hb
  obtain ⟨d, hd, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, he, heeq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨U, hU, hUeq⟩ := unaryTrue
  obtain ⟨C, hC, hCiff⟩ := MPP.Solutions.Pnp028.main
  obtain ⟨L227, hL227, hL227eq⟩ := MPP.Solutions.Pnp227.main
  have hdd : PT (fun z => d (d z)) := comp hd hd
  obtain ⟨P1, hP1, hP1eq⟩ := pairP hdd he
  have hW : PT (fun z => e (d z)) := comp hd he
  have hUa : PT (fun z => U (a (P1 z))) := comp (comp hP1 ha) hU
  obtain ⟨Pm, hPm, hPmeq⟩ := pairP hUa hW
  have hUb : PT (fun z => U (b (P1 z))) := comp (comp hP1 hb) hU
  obtain ⟨Pm', hPm', hPm'eq⟩ := pairP hUb hW
  have hCa : InP (fun z => L227 (Pm z)) := langComp hL227 hPm
  have hCb : InP (fun z => L227 (Pm' z)) := langComp hL227 hPm'
  have hG : InP (fun z => C (P1 z)) := langComp hC hP1
  have hCab : InP (fun z => L227 (Pm z) && L227 (Pm' z)) :=
    MPP.Solutions.Pnp011.main _ _ hCa hCb
  have hLH : InP (fun z => C (P1 z) && (L227 (Pm z) && L227 (Pm' z))) :=
    MPP.Solutions.Pnp011.main _ _ hG hCab
  obtain ⟨h, hh, hheq⟩ := langMap _ hLH
  obtain ⟨f, hf, hfeq⟩ := MPP.Solutions.Pnp229.main h hh
  refine ⟨f, hf, fun x w => ?_⟩
  have hterm : ∀ m : ℕ, (h (pair (pair x w) (List.replicate m true))).headD false =
      (decide (m ≤ x.length) && (w.getD (a (pair x (List.replicate m true))).length false &&
        w.getD (b (pair x (List.replicate m true))).length false)) := by
    intro m
    have hd1 : d (pair (pair x w) (List.replicate m true)) = pair x w := hdeq _ _
    have hd2 : d (pair x w) = x := hdeq _ _
    have hdd' : d (d (pair (pair x w) (List.replicate m true))) = x := by rw [hd1, hd2]
    have he1 : e (pair (pair x w) (List.replicate m true)) = List.replicate m true :=
      heeq _ _
    have hew : e (d (pair (pair x w) (List.replicate m true))) = w := by
      rw [hd1, heeq]
    have hP1Y : P1 (pair (pair x w) (List.replicate m true)) =
        pair x (List.replicate m true) := by
      rw [hP1eq, hdd', he1]
    have hPmY : Pm (pair (pair x w) (List.replicate m true)) =
        pair (U (a (pair x (List.replicate m true)))) w := by
      simp only [hPmeq, hP1Y, hew]
    have hPm'Y : Pm' (pair (pair x w) (List.replicate m true)) =
        pair (U (b (pair x (List.replicate m true)))) w := by
      simp only [hPm'eq, hP1Y, hew]
    have hC1 : C (P1 (pair (pair x w) (List.replicate m true))) =
        decide (m ≤ x.length) := by
      rw [hP1Y]
      apply Bool.eq_iff_iff.mpr
      rw [hCiff, List.length_replicate, decide_eq_true_eq]
    have hL1 : L227 (Pm (pair (pair x w) (List.replicate m true))) =
        w.getD (a (pair x (List.replicate m true))).length false := by
      rw [hPmY, hUeq, hL227eq]
    have hL2 : L227 (Pm' (pair (pair x w) (List.replicate m true))) =
        w.getD (b (pair x (List.replicate m true))).length false := by
      rw [hPm'Y, hUeq, hL227eq]
    rw [hheq]
    simp only [List.headD_cons]
    rw [hC1, hL1, hL2]
  have hlen : x.length ≤ (pair x w).length := by
    simp [pair]
    omega
  rw [hfeq (pair x w)]
  congr 1
  simp only [hterm]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, hle, hc⟩
    exact ⟨m, by omega, hc⟩
  · rintro ⟨m, hm, hc⟩
    exact ⟨m, by omega, by omega, hc⟩

end MPP.Solutions.Pnp237
