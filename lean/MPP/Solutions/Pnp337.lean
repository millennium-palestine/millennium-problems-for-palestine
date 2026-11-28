import Mathlib
import MPP.Solutions.Pnp213
import MPP.Solutions.Pnp290

namespace MPP.Solutions.Pnp337

-- helper: stack independence of balanced blocks (the proof of pnp-325, inlined)
theorem stackind : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool),
    F = (fun (st : List Bool × List Bool × Option Bool) (b : Bool) => match st.2.2 with | none => (st.1, st.2.1, some b) | some a => if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none) else (st.1, st.2.1, none)) else (if b then (st.1.headD false :: st.1, st.2.1, none) else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (H : Bool × Bool → ℤ), H = (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) →
    ∀ (Rel : List (Bool × Bool) → List Bool → Bool → Bool → Prop),
    (∀ (q : List (Bool × Bool)) (T : List Bool) (v g : Bool), Rel q T v g ↔ ∃ w : List Bool, w.length = q.countP (fun x : Bool × Bool => !x.1 && !x.2) ∧ ∃ w' : List Bool, (q.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: T, w, none) = (g :: T, w', none)) →
    ∀ (q : List (Bool × Bool)), (∀ j, j ≤ q.length → 0 ≤ ((q.map H).take j).sum) → (q.map H).sum = 0 →
    ∀ (t t' : List Bool) (v g : Bool), Rel q t v g → Rel q t' v g := by
  intro F hF H hH Rel hRel
  subst hH
  have hnil : ∀ (t t' : List Bool) (v g : Bool), Rel [] t v g → Rel [] t' v g := by
    intro t t' v g h
    rw [hRel] at h
    rw [hRel]
    obtain ⟨w, hw, w', hf⟩ := h
    subst hF
    simp at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨w, hw, w, by simp⟩
  have s323 : ∀ (a c : Bool × Bool) (mid : List (Bool × Bool)), a.1 = false → c = (true, true) →
      (mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
      (∀ j, j ≤ mid.length → 0 ≤ ((mid.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      (∀ (T T' : List Bool) (u g : Bool), Rel mid T u g → Rel mid T' u g) →
      ∀ (t t' : List Bool) (v g : Bool), Rel (a :: (mid ++ [c])) t v g → Rel (a :: (mid ++ [c])) t' v g := by
    intro a c mid ha hc hms hmn IH t t' v g h
    have h212 := MPP.Solutions.Pnp212.main F hF a c mid ha hc hms hmn
    rw [hRel] at h
    rw [hRel]
    rw [h212 v g t] at h
    rw [h212 v g t']
    obtain ⟨u, hu, g', hmid, hg⟩ := h
    refine ⟨u, hu, g', ?_, hg⟩
    exact (hRel mid (v :: t') u g').mp (IH (v :: t) (v :: t') u g' ((hRel mid (v :: t) u g').mpr hmid))
  have s324 : ∀ (p s : List (Bool × Bool)),
      (∀ j, j ≤ p.length → 0 ≤ ((p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      (p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
      (∀ j, j ≤ s.length → 0 ≤ ((s.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      (s.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
      (∀ (T T' : List Bool) (u g : Bool), Rel p T u g → Rel p T' u g) →
      (∀ (T T' : List Bool) (u g : Bool), Rel s T u g → Rel s T' u g) →
      ∀ (t t' : List Bool) (v g : Bool), Rel (p ++ s) t v g → Rel (p ++ s) t' v g := by
    intro p s hp1 hp2 hs1 hs2 IHp IHs t t' v g h
    have h201 := MPP.Solutions.Pnp201.main F hF p s hp1 hp2 hs1 hs2 t v g
    have h201' := MPP.Solutions.Pnp201.main F hF p s hp1 hp2 hs1 hs2 t' v g
    rw [hRel] at h
    rw [hRel]
    rw [h201] at h
    rw [h201']
    obtain ⟨g1, hp, hs⟩ := h
    exact ⟨g1, (hRel p t' v g1).mp (IHp t t' v g1 ((hRel p t v g1).mpr hp)),
      (hRel s t' g1 g).mp (IHs t t' g1 g ((hRel s t g1 g).mpr hs))⟩
  have key : ∀ n : ℕ, ∀ (q : List (Bool × Bool)), q.length ≤ n →
      (∀ j, j ≤ q.length → 0 ≤ ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
      ∀ (t t' : List Bool) (v g : Bool), Rel q t v g → Rel q t' v g := by
    intro n
    induction n with
    | zero =>
      intro q hq _ _ t t' v g h
      have hq0 : q = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hq0
      exact hnil t t' v g h
    | succ n ih =>
      intro q hq hnn hsum t t' v g h
      rcases Nat.eq_zero_or_pos q.length with h0 | hpos
      · have hq0 : q = [] := List.eq_nil_of_length_eq_zero h0
        subst hq0
        exact hnil t t' v g h
      · rcases MPP.Solutions.Pnp211.main q hpos hnn hsum with h1 | ⟨a, c, mid, hq', ha, hc, hms, hmn⟩ | ⟨p, s, hq', hp0, hs0, hpn, hpsum, hsn, hssum⟩
        · subst h1
          rw [hRel] at h
          rw [hRel]
          obtain ⟨w, hw, w', hf⟩ := h
          have key2 : ∀ (t : List Bool) (v : Bool) (w : List Bool),
              ([(true, false)].flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: t, w, none) = (v :: t, w, none) := by
            intro t v w
            subst hF
            rfl
          rw [key2] at hf
          have hvg : v = g := by
            have := congrArg (fun x : List Bool × List Bool × Option Bool => x.1.headD false) hf
            simpa using this
          exact ⟨w, hw, w, by rw [key2, ← hvg]⟩
        · subst hq'
          have hlen : mid.length ≤ n := by
            simp only [List.length_cons, List.length_append, List.length_singleton] at hq
            omega
          exact s323 a c mid ha hc hms hmn (fun T T' u g h => ih mid hlen hmn hms T T' u g h) t t' v g h
        · subst hq'
          have hlenp : p.length ≤ n := by
            simp only [List.length_append] at hq
            omega
          have hlens : s.length ≤ n := by
            simp only [List.length_append] at hq
            omega
          exact s324 p s hpn hpsum hsn hssum
            (fun T T' u g h => ih p hlenp hpn hpsum T T' u g h)
            (fun T T' u g h => ih s hlens hsn hssum T T' u g h) t t' v g h
  intro q hnn hsum t t' v g h
  exact key _ q le_rfl hnn hsum t t' v g h

theorem main :
    ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool),
    F = (fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a => if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none) else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none) else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (H : Bool × Bool → ℤ), H = (fun r => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) →
    ∀ (q : List (Bool × Bool)) (S : ℕ → ℕ → List (Bool × Bool)) (X : ℕ → ℕ → Bool × Bool → Prop),
    (∀ i j, S i j = (q.drop i).take (j - i)) →
    (∀ i j r, X i j r ↔ j ≤ q.length ∧
      (∀ k, k ≤ (S i j).length → 0 ≤ (((S i j).map H).take k).sum) ∧ ((S i j).map H).sum = 0 ∧
      ∃ w : List Bool, w.length = (S i j).countP (fun x => !x.1 && !x.2) ∧
        ∃ w' : List Bool, ((S i j).flatMap fun r => [r.1, r.2]).foldl F ([r.1], w, none) = ([r.2], w', none)) →
    ∀ i j r, i + 2 ≤ j →
      (X i j r ↔
        ((∃ u : Bool, ((∃ b : Bool, S i (i + 1) = [(false, b)]) ∧
            (∀ b : Bool, S i (i + 1) = [(false, b)] → b = true → u = r.1) ∧ S (j - 1) j = [(true, true)]) ∧
          ∃ g' : Bool, X (i + 1) (j - 1) (u, g') ∧ r.2 = !(g' && r.1)) ∨
         (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, X i k (r.1, g1) ∧ X k j (g1, r.2)))) := by
  intro F hF H hH q S X hS hX i j r hij
  have hL : ∀ a b, a ≤ b → b ≤ q.length → (S a b).length = b - a := by
    intro a b hab hb
    rw [hS, List.length_take, List.length_drop]
    omega
  have hA : ∀ a k b, a ≤ k → k ≤ b → S a b = S a k ++ S k b := by
    intro a k b hak hkb
    simp only [hS]
    exact MPP.Solutions.Pnp290.slice_split q a k b hak hkb
  have hsplitv : ∀ a b, a + 2 ≤ b → b ≤ q.length →
      S a b = S a (a + 1) ++ (S (a + 1) (b - 1) ++ S (b - 1) b) := by
    intro a b h1 h2
    rw [hA a (a + 1) b (by omega) (by omega), hA (a + 1) (b - 1) b (by omega) (by omega)]
  have hlen1 : ∀ a, a + 1 ≤ q.length → (S a (a + 1)).length = 1 := by
    intro a h
    have := hL a (a + 1) (by omega) h
    omega
  have hHa : ∀ b : Bool, H (false, b) = 1 := by
    intro b
    rw [hH]
    simp
  have hHc : H (true, true) = -1 := by
    rw [hH]
    simp
  constructor
  · intro hXr
    obtain ⟨hjL, hnn, hz, w, hw, w', hrun⟩ := (hX i j r).mp hXr
    have hlij := hL i j (by omega) hjL
    have hlen : 0 < (S i j).length := by omega
    rcases (MPP.Solutions.Pnp213.main F hF H hH (S i j) hlen hnn hz r.1 r.2 []).mp ⟨w, hw, w', hrun⟩ with
      ⟨hq1, _⟩ | ⟨a, c, mid, hq, ha1, hc, hmid, hmidnn, u, hu, g', ⟨w1, hw1, w2, hr1⟩, hg⟩ |
      ⟨p, s, hq, hp0, hs0, hpn, hpsum, hsn, hssum, g1, ⟨wp, hwp, wp', hrp⟩, ⟨ws, hws, ws', hrs⟩⟩
    · rw [hq1] at hlij
      simp at hlij
      omega
    · obtain ⟨a1, a2⟩ := a
      obtain ⟨c1, c2⟩ := c
      dsimp only at ha1
      subst ha1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
      have e := hsplitv i j hij hjL
      rw [hq] at e
      have hmidlen : mid.length = j - i - 2 := by
        have := hL i j (by omega) hjL
        rw [hq] at this
        simp at this
        omega
      have e2 : [(false, a2)] ++ (mid ++ [(true, true)]) = S i (i + 1) ++ (S (i + 1) (j - 1) ++ S (j - 1) j) := e
      obtain ⟨hSi, hrest⟩ := List.append_inj e2 (by simp [hlen1 i (by omega)])
      have hlenm : mid.length = (S (i + 1) (j - 1)).length := by
        rw [hL (i + 1) (j - 1) (by omega) (by omega)]
        omega
      obtain ⟨hmid_eq, hc_eq⟩ := List.append_inj hrest hlenm
      have hSi' : S i (i + 1) = [(false, a2)] := hSi.symm
      have hSc : S (j - 1) j = [(true, true)] := hc_eq.symm
      refine Or.inl ⟨u, ⟨⟨a2, hSi'⟩, ?_, hSc⟩, g', ?_, hg⟩
      · intro b hb hb1
        have hb' : [(false, b)] = [(false, a2)] := hb.symm.trans hSi'
        have hba : b = a2 := by simpa using hb'
        subst hba
        exact hu hb1
      · refine (hX (i + 1) (j - 1) (u, g')).mpr ⟨by omega, ?_, ?_, ?_⟩
        · rw [← hmid_eq]
          exact hmidnn
        · rw [← hmid_eq]
          exact hmid
        · rw [← hmid_eq]
          obtain ⟨w3, hw3, w3', hr3⟩ := stackind F hF H hH
            (fun q T v g => ∃ w : List Bool, w.length = q.countP (fun x : Bool × Bool => !x.1 && !x.2) ∧ ∃ w' : List Bool, (q.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: T, w, none) = (g :: T, w', none))
            (fun _ _ _ _ => Iff.rfl) mid hmidnn hmid [r.1] [] u g' ⟨w1, hw1, w2, hr1⟩
          exact ⟨w3, hw3, w3', hr3⟩
    · have hlen2 := hL i j (by omega) hjL
      rw [hq] at hlen2
      simp at hlen2
      have hk := hA i (i + p.length) j (by omega) (by omega)
      have hlk : (S i (i + p.length)).length = p.length := by
        rw [hL i (i + p.length) (by omega) (by omega)]
        omega
      have e := hq.symm.trans hk
      obtain ⟨hpS, hsS⟩ := List.append_inj e hlk.symm
      refine Or.inr ⟨i + p.length, by omega, by omega, g1, ?_, ?_⟩
      · refine (hX i (i + p.length) (r.1, g1)).mpr ⟨by omega, ?_, ?_, ?_⟩
        · rw [← hpS]
          exact hpn
        · rw [← hpS]
          exact hpsum
        · rw [← hpS]
          exact ⟨wp, hwp, wp', hrp⟩
      · refine (hX (i + p.length) j (g1, r.2)).mpr ⟨hjL, ?_, ?_, ?_⟩
        · rw [← hsS]
          exact hsn
        · rw [← hsS]
          exact hssum
        · rw [← hsS]
          exact ⟨ws, hws, ws', hrs⟩
  · intro hR
    rcases hR with ⟨u, ⟨⟨b, hb⟩, hu, hc⟩, g', hX', hg⟩ | ⟨k, hik, hkj, g1, hXik, hXkj⟩
    · have hjL : j ≤ q.length := by
        have h1 : (S (j - 1) j).length = 1 := by simp [hc]
        rw [hS, List.length_take, List.length_drop] at h1
        omega
      obtain ⟨hmn, hmz, w, hw, w', hr⟩ : (∀ k, k ≤ (S (i + 1) (j - 1)).length → 0 ≤ (((S (i + 1) (j - 1)).map H).take k).sum) ∧ ((S (i + 1) (j - 1)).map H).sum = 0 ∧ ∃ w : List Bool, w.length = (S (i + 1) (j - 1)).countP (fun x => !x.1 && !x.2) ∧ ∃ w' : List Bool, ((S (i + 1) (j - 1)).flatMap fun r => [r.1, r.2]).foldl F ([u], w, none) = ([g'], w', none) := by
        obtain ⟨_, h2, h3, h4⟩ := (hX (i + 1) (j - 1) (u, g')).mp hX'
        exact ⟨h2, h3, h4⟩
      have eqS : S i j = (false, b) :: (S (i + 1) (j - 1) ++ [(true, true)]) := by
        rw [hsplitv i j hij hjL, hb, hc, List.singleton_append]
      have hHmap : (S i j).map H = 1 :: ((S (i + 1) (j - 1)).map H ++ [-1]) := by
        rw [eqS]
        simp [hHa, hHc]
      have hwb := MPP.Solutions.Pnp290.walk_block ((S (i + 1) (j - 1)).map H) (by simpa using hmn) (by simpa using hmz)
      have hnn' : ∀ k, k ≤ (S i j).length → 0 ≤ (((S i j).map H).take k).sum := by
        intro k hk
        have hl1' := hL i j (by omega) hjL
        have hl2' := hL (i + 1) (j - 1) (by omega) (by omega)
        rw [hHmap]
        exact hwb k (by simp only [List.length_cons, List.length_append, List.length_map, List.length_singleton]; omega)
      have hsum' : ((S i j).map H).sum = 0 := by
        rw [hHmap]
        simp [hmz]
      have hlen' : 0 < (S i j).length := by
        have := hL i j (by omega) hjL
        omega
      obtain ⟨w3, hw3, w3', hr3⟩ := stackind F hF H hH
        (fun q T v g => ∃ w : List Bool, w.length = q.countP (fun x : Bool × Bool => !x.1 && !x.2) ∧ ∃ w' : List Bool, (q.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (v :: T, w, none) = (g :: T, w', none))
        (fun _ _ _ _ => Iff.rfl) (S (i + 1) (j - 1)) hmn hmz [] [r.1] u g' ⟨w, hw, w', hr⟩
      have hr213 := (MPP.Solutions.Pnp213.main F hF H hH (S i j) hlen' hnn' hsum' r.1 r.2 []).mpr
        (Or.inr (Or.inl ⟨(false, b), (true, true), S (i + 1) (j - 1), eqS, rfl, rfl, hmz, hmn,
          u, fun h => hu b hb h, g', ⟨w3, hw3, w3', hr3⟩, hg⟩))
      exact (hX i j r).mpr ⟨hjL, hnn', hsum', hr213⟩
    · obtain ⟨hkL, hn1, hz1, w1, hw1, w1', hr1⟩ := (hX i k (r.1, g1)).mp hXik
      obtain ⟨hjL, hn2, hz2, w2, hw2, w2', hr2⟩ := (hX k j (g1, r.2)).mp hXkj
      have hsplit := hA i k j (by omega) (by omega)
      have hl1 : 0 < (S i k).length := by
        have := hL i k (by omega) hkL
        omega
      have hl2 : 0 < (S k j).length := by
        have := hL k j (by omega) hjL
        omega
      have hA1 : ∀ l, l ≤ ((S i k).map H).length → 0 ≤ (((S i k).map H).take l).sum := by
        intro l hl
        simp only [List.length_map] at hl
        exact hn1 l hl
      have hB1 : ∀ l, l ≤ ((S k j).map H).length → 0 ≤ (((S k j).map H).take l).sum := by
        intro l hl
        simp only [List.length_map] at hl
        exact hn2 l hl
      have hwa := MPP.Solutions.Pnp290.walk_append ((S i k).map H) ((S k j).map H) hA1 hB1 hz1
      have hnn_ij : ∀ l, l ≤ (S i j).length → 0 ≤ (((S i j).map H).take l).sum := by
        intro l hl
        rw [hsplit, List.map_append]
        rw [hsplit] at hl
        exact hwa l (by simpa using hl)
      have hsum_ij : ((S i j).map H).sum = 0 := by
        simp [hsplit, List.map_append, List.sum_append, hz1, hz2]
      have hlen' : 0 < (S i j).length := by
        have := hL i j (by omega) hjL
        omega
      have hr213 := (MPP.Solutions.Pnp213.main F hF H hH (S i j) hlen' hnn_ij hsum_ij r.1 r.2 []).mpr
        (Or.inr (Or.inr ⟨S i k, S k j, hsplit, hl1, hl2, hn1, hz1, hn2, hz2, g1,
          ⟨w1, hw1, w1', hr1⟩, ⟨w2, hw2, w2', hr2⟩⟩))
      exact (hX i j r).mpr ⟨hjL, hnn_ij, hsum_ij, hr213⟩

end MPP.Solutions.Pnp337
