import Mathlib
import MPP.Solutions.Pnp211

namespace MPP.Solutions.Pnp290

-- helper: the slice (i, j) of a list splits at an inner point k
theorem slice_split (q : List (Bool × Bool)) (i k j : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
    (q.drop i).take (j - i) = (q.drop i).take (k - i) ++ (q.drop k).take (j - k) := by
  have e : j - i = (k - i) + (j - k) := by omega
  have hk : (q.drop i).drop (k - i) = q.drop k := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [e, List.take_add, hk]

-- helper: the slice (i, j) of length at least two is its first pair, the interior, and its last pair
theorem slice_ends (q : List (Bool × Bool)) (i j : ℕ) (hij : i + 2 ≤ j) (hq : j ≤ q.length) :
    (q.drop i).take (j - i) = (q.drop i).take 1 ++ (q.drop (i + 1)).take (j - i - 2) ++ (q.drop (j - 1)).take 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + 2 + m := ⟨j - (i + 2), by omega⟩
  have e1 : i + 2 + m - i = 1 + (m + 1) := by omega
  have e2 : i + 2 + m - i - 2 = m := by omega
  have e3 : i + 2 + m - 1 = (i + 1) + m := by omega
  have h1 : (q.drop i).take (1 + (m + 1)) = (q.drop i).take 1 ++ (q.drop (i + 1)).take (m + 1) := by
    rw [List.take_add, List.drop_drop]
  have h2 : (q.drop (i + 1)).take (m + 1) = (q.drop (i + 1)).take m ++ (q.drop (i + 1 + m)).take 1 := by
    rw [List.take_add, List.drop_drop]
  rw [e1, h1, h2, e3, show 1 + (m + 1) - 2 = m by omega, List.append_assoc]

-- helper: a walk that stays nonnegative and ends at zero, followed by a down step, wrapped by an up step
theorem walk_block (M : List ℤ) (hM : ∀ l, l ≤ M.length → 0 ≤ (M.take l).sum) (hz : M.sum = 0) :
    ∀ l, l ≤ (1 :: (M ++ [-1])).length → 0 ≤ ((1 :: (M ++ [-1])).take l).sum := by
  intro l hl
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    rw [List.take_succ_cons, List.sum_cons]
    by_cases hm : m ≤ M.length
    · rw [List.take_append_of_le_length hm]
      have := hM m hm
      linarith
    · have hm' : m = M.length + 1 := by simp at hl; omega
      subst hm'
      rw [List.take_of_length_le (by simp)]
      simp [hz]

-- helper: concatenation of two nonnegative zero-sum walks
theorem walk_append (A B : List ℤ) (hA : ∀ l, l ≤ A.length → 0 ≤ (A.take l).sum)
    (hB : ∀ l, l ≤ B.length → 0 ≤ (B.take l).sum) (hAs : A.sum = 0) :
    ∀ l, l ≤ (A ++ B).length → 0 ≤ ((A ++ B).take l).sum := by
  intro l hl
  by_cases hm : l ≤ A.length
  · rw [List.take_append_of_le_length hm]
    exact hA l hm
  · have hm' : A.length ≤ l := not_le.mp hm |>.le
    rw [List.take_append, List.take_of_length_le hm', List.sum_append, hAs, zero_add]
    have hl' : l - A.length ≤ B.length := by simp at hl; omega
    exact hB _ hl'

-- helper: a primitive block, an up pair, a walk M and a down pair, read through the step values
theorem walk_pairs (f : Bool × Bool → ℤ) (hf : ∀ b : Bool, f (false, b) = 1) (hg : f (true, true) = -1) (b : Bool)
    (M : List (Bool × Bool))
    (hM : ∀ l, l ≤ (M.map f).length → 0 ≤ ((M.map f).take l).sum) (hz : (M.map f).sum = 0) :
    (∀ l, l ≤ M.length + 2 → 0 ≤ ((([(false, b)] ++ M ++ [(true, true)]).map f).take l).sum) ∧
    (([(false, b)] ++ M ++ [(true, true)]).map f).sum = 0 := by
  have hw := walk_block (M.map f) hM hz
  simp only [List.singleton_append, List.map_cons, List.map_append, List.map_nil, hf, hg,
    List.sum_cons, List.sum_append, List.sum_nil]
  refine ⟨fun l hl => hw l ?_, ?_⟩
  · simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] at hl ⊢
    omega
  · simp [hz]

theorem main : ∀ (H : Bool × Bool → ℤ), (∀ r : Bool × Bool, H r = if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) →
    ∀ (q : List (Bool × Bool)) (B : ℕ → ℕ → Prop),
    (∀ a b : ℕ, B a b ↔ ((∀ l, l ≤ b - a → 0 ≤ ((((q.drop a).take (b - a)).map H).take l).sum) ∧
      (((q.drop a).take (b - a)).map H).sum = 0)) →
    ∀ i j : ℕ, i + 2 ≤ j → j ≤ q.length →
    (B i j ↔ ((∃ b : Bool, (q.drop i).take 1 = [(false, b)]) ∧ (q.drop (j - 1)).take 1 = [(true, true)] ∧ B (i + 1) (j - 1)) ∨
      (∃ k : ℕ, i < k ∧ k < j ∧ B i k ∧ B k j)) := by
  intro H hH q B hB i j hij hq
  have hHf : H = fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1 := funext hH
  subst hHf
  rw [hB i j]
  have hlen : ((q.drop i).take (j - i)).length = j - i := by simp; omega
  constructor
  · rintro ⟨hnn, hz⟩
    have hs : 0 < ((q.drop i).take (j - i)).length := by rw [hlen]; omega
    have hnn' : ∀ l, l ≤ ((q.drop i).take (j - i)).length →
        0 ≤ ((((q.drop i).take (j - i)).map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take l).sum := by
      rw [hlen]; exact hnn
    have hz' : (((q.drop i).take (j - i)).map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 := hz
    rcases MPP.Solutions.Pnp211.main _ hs hnn' hz' with h | ⟨a, c, mid, heq, ha, hc, hmz, hmnn⟩ | ⟨p, s, heq, hp0, hs0, hpn, hpz, hsn, hsz⟩
    · exfalso
      have := congrArg List.length h
      rw [hlen] at this
      simp at this
      omega
    · rw [slice_ends q i j hij hq] at heq
      have heq' : (q.drop i).take 1 ++ ((q.drop (i + 1)).take (j - i - 2) ++ (q.drop (j - 1)).take 1) =
          [a] ++ (mid ++ [c]) := by
        rw [← List.append_assoc]
        exact heq
      have hA1 : ((q.drop i).take 1).length = 1 := by simp; omega
      have hC1 : ((q.drop (j - 1)).take 1).length = 1 := by simp; omega
      obtain ⟨hA, hMC⟩ := List.append_inj heq' (by simp [hA1])
      obtain ⟨hM, hC⟩ := List.append_inj' hMC (by simp [hC1])
      have ha' : a = (false, a.2) := Prod.ext ha rfl
      have hlm : mid.length = j - i - 2 := by rw [← hM]; simp; omega
      have hBM : B (i + 1) (j - 1) := by
        rw [hB]
        have e : j - 1 - (i + 1) = j - i - 2 := by omega
        rw [e, hM]
        exact ⟨fun l hl => hmnn l (by omega), hmz⟩
      left
      refine ⟨⟨a.2, ?_⟩, ?_, hBM⟩
      · rw [hA]
        exact congrArg (fun x => [x]) ha'
      · rw [hC, hc]
    · have hl := congrArg List.length heq
      rw [hlen, List.length_append] at hl
      have hsplit := slice_split q i (i + p.length) j (by omega) (by omega)
      have hcat : (q.drop i).take (i + p.length - i) ++ (q.drop (i + p.length)).take (j - (i + p.length)) = p ++ s := by
        rw [← hsplit]
        exact heq
      have hlp : ((q.drop i).take (i + p.length - i)).length = p.length := by simp; omega
      obtain ⟨hpk, hsk⟩ := List.append_inj hcat hlp
      right
      refine ⟨i + p.length, by omega, by omega, ?_, ?_⟩
      · rw [hB, hpk]
        exact ⟨fun l hl => hpn l (by omega), hpz⟩
      · rw [hB, hsk]
        exact ⟨fun l hl => hsn l (by omega), hsz⟩
  · rintro (⟨⟨b, hA⟩, hC, hBM⟩ | ⟨k, hik, hkj, hBik, hBkj⟩)
    · rw [hB] at hBM
      obtain ⟨hMn, hMz⟩ := hBM
      have e : j - 1 - (i + 1) = j - i - 2 := by omega
      rw [e] at hMn hMz
      rw [slice_ends q i j hij hq, hA, hC]
      have hlM : ((q.drop (i + 1)).take (j - i - 2)).length = j - i - 2 := by simp; omega
      have key := walk_pairs (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)
        (fun b => by cases b <;> simp) (by simp) b ((q.drop (i + 1)).take (j - i - 2))
        (fun l hl => hMn l (by rw [List.length_map, hlM] at hl; exact hl)) hMz
      exact ⟨fun l hl => key.1 l (by rw [hlM]; omega), key.2⟩
    · rw [hB] at hBik hBkj
      obtain ⟨hn1, hz1⟩ := hBik
      obtain ⟨hn2, hz2⟩ := hBkj
      have hlX : ((q.drop i).take (k - i)).length = k - i := by simp; omega
      have hlY : ((q.drop k).take (j - k)).length = j - k := by simp; omega
      rw [slice_split q i k j (by omega) (by omega), List.map_append]
      refine ⟨fun l hl => walk_append _ _
        (fun l' hl' => hn1 l' (by rw [List.length_map, hlX] at hl'; exact hl'))
        (fun l' hl' => hn2 l' (by rw [List.length_map, hlY] at hl'; exact hl')) hz1 l ?_, ?_⟩
      · rw [List.length_append, List.length_map, List.length_map, hlX, hlY]
        omega
      · rw [List.sum_append, hz1, hz2, zero_add]

end MPP.Solutions.Pnp290
