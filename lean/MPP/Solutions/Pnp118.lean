import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp118

open Turing

/-- Control label `t` of the prefix machine for a fixed `k`, as an element of `Fin (k + 2)`.
Labels `t < k` move one input symbol to the accumulator (stack 2). Label `k` discards the rest of
the input (stack 0). Label `k + 1` pops the accumulator onto the output (stack 1). -/
def lab (k t : ℕ) : Fin (k + 2) := ⟨min t (k + 1), by have := Nat.min_le_right t (k + 1); omega⟩

/-- Program of the prefix map. -/
def prog (k : ℕ) : Fin (k + 2) → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool) :=
  fun i =>
    if i.val < k then
      .pop 0 (fun _ h => h)
        (.branch (fun s => s.isSome)
          (.push 2 (fun s => s.getD false) (.goto fun _ => lab k (i.val + 1)))
          (.goto fun _ => lab k k))
    else if i.val = k then
      .pop 0 (fun _ h => h)
        (.branch (fun s => s.isSome)
          (.goto fun _ => lab k k)
          (.goto fun _ => lab k (k + 1)))
    else
      .pop 2 (fun _ h => h)
        (.branch (fun s => s.isSome)
          (.push 1 (fun s => s.getD false) (.goto fun _ => lab k (k + 1)))
          (.load (fun _ => none) .halt))

/-- The prefix map as a finite machine: stacks `0` (input), `1` (output), `2` (accumulator). -/
def tm (k : ℕ) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin (k + 2)
  main := lab k 0
  σ := Option Bool
  initialState := none
  m := prog k

/-- Configuration with label `lab k t`, state `v`, input `R`, output `O`, accumulator `B`. -/
def cfgN (k t : ℕ) (v : Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool) :=
  ⟨some (lab k t), v, ![R, O, B]⟩

theorem lab_val (k t : ℕ) (ht : t ≤ k + 1) : (lab k t).val = t := by
  unfold lab
  show min t (k + 1) = t
  omega

theorem step_count (k t : ℕ) (ht : t < k) (v : Option Bool) (a : Bool) (R O B : List Bool) :
    TM2.step (prog k) (cfgN k t v (a :: R) O B) = some (cfgN k (t + 1) (some a) R O (a :: B)) := by
  have hv := lab_val k t (by omega)
  simp [TM2.step, TM2.stepAux, prog, cfgN, hv, ht] <;> (funext j; fin_cases j <;> simp)

theorem step_count_nil (k t : ℕ) (ht : t < k) (v : Option Bool) (O B : List Bool) :
    TM2.step (prog k) (cfgN k t v [] O B) = some (cfgN k k none [] O B) := by
  have hv := lab_val k t (by omega)
  simp [TM2.step, TM2.stepAux, prog, cfgN, hv, ht] <;> (funext j; fin_cases j <;> simp)

theorem step_disc_cons (k : ℕ) (v : Option Bool) (a : Bool) (R O B : List Bool) :
    TM2.step (prog k) (cfgN k k v (a :: R) O B) = some (cfgN k k (some a) R O B) := by
  have hv := lab_val k k (by omega)
  have h1 : ¬ (k < k) := lt_irrefl k
  simp [TM2.step, TM2.stepAux, prog, cfgN, hv, h1] <;> (funext j; fin_cases j <;> simp)

theorem step_disc_nil (k : ℕ) (v : Option Bool) (O B : List Bool) :
    TM2.step (prog k) (cfgN k k v [] O B) = some (cfgN k (k + 1) none [] O B) := by
  have hv := lab_val k k (by omega)
  have h1 : ¬ (k < k) := lt_irrefl k
  have h2 : k ≠ k + 1 := by omega
  simp [TM2.step, TM2.stepAux, prog, cfgN, hv, h1, h2] <;> (funext j; fin_cases j <;> simp)

theorem step_rev_push (k : ℕ) (v : Option Bool) (a : Bool) (O B : List Bool) :
    TM2.step (prog k) (cfgN k (k + 1) v [] O (a :: B)) = some (cfgN k (k + 1) (some a) [] (a :: O) B) := by
  have hv := lab_val k (k + 1) (by omega)
  have h1 : ¬ (k + 1 < k) := by omega
  have h2 : ¬ (k + 1 = k) := by omega
  simp [TM2.step, TM2.stepAux, prog, cfgN, hv, h1, h2] <;> (funext j; fin_cases j <;> simp)

theorem step_rev_end (k : ℕ) (v : Option Bool) (O : List Bool) :
    TM2.step (prog k) (cfgN k (k + 1) v [] O []) = some ⟨none, none, ![[], O, []]⟩ := by
  have hv := lab_val k (k + 1) (by omega)
  have h1 : ¬ (k + 1 < k) := by omega
  have h2 : ¬ (k + 1 = k) := by omega
  simp [TM2.step, TM2.stepAux, prog, cfgN, hv, h1, h2] <;> (funext j; fin_cases j <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (k n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool)) :=
  (fun o => o.bind (TM2.step (prog k)))^[n] (some c)

theorem rn_succ_step {k n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool)}
    (h : TM2.step (prog k) c = some c') : rn k (n + 1) c = rn k n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {k m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool)}
    (h : rn k m c = some c') : rn k (n + m) c = rn k n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

theorem rn_trans {k m n : ℕ}
    {c c' c'' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin (k + 2)) (Option Bool)}
    (h1 : rn k m c = some c') (h2 : rn k n c' = some c'') : rn k (n + m) c = some c'' := by
  rw [rn_add h1]
  exact h2

/-- Counting phase: from label `t ≤ k`, after at most `k - t + 1` steps the machine is at label `k`,
with the first `k - t` symbols of the input moved (reversed) onto the accumulator. -/
theorem phaseA (k : ℕ) : ∀ (w : List Bool) (t : ℕ) (B O : List Bool) (v : Option Bool), t ≤ k →
    ∃ s v', s ≤ k - t + 1 ∧
      rn k s (cfgN k t v w O B) = some (cfgN k k v' (w.drop (k - t)) O ((w.take (k - t)).reverse ++ B))
  | [], t, B, O, v, ht => by
      rcases Nat.lt_or_ge t k with h | h
      · refine ⟨1, none, by omega, ?_⟩
        rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step_count_nil k t h v O B)]
        simp [rn]
      · have he : t = k := by omega
        refine ⟨0, v, by omega, ?_⟩
        simp [rn, he]
  | a :: R, t, B, O, v, ht => by
      rcases Nat.lt_or_ge t k with h | h
      · obtain ⟨s, v', hs, hrun⟩ := phaseA k R (t + 1) (a :: B) O (some a) (by omega)
        refine ⟨s + 1, v', by omega, ?_⟩
        rw [rn_succ_step (step_count k t h v a R O B), hrun]
        have e : k - t = (k - (t + 1)) + 1 := by omega
        rw [e, List.drop_succ_cons, List.take_succ_cons]
        simp [List.reverse_cons, List.append_assoc]
      · have he : t = k := by omega
        refine ⟨0, v, by omega, ?_⟩
        simp [rn, he]

/-- Discarding phase: from label `k`, the rest of the input is popped and dropped in `|R| + 1` steps,
and the machine reaches label `k + 1` with an empty input. -/
theorem phaseD (k : ℕ) (B : List Bool) : ∀ (R O : List Bool) (v : Option Bool),
    rn k (R.length + 1) (cfgN k k v R O B) = some (cfgN k (k + 1) none [] O B)
  | [], O, v => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step_disc_nil k v O B)]
      simp [rn]
  | a :: R, O, v => by
      rw [show (a :: R).length + 1 = (R.length + 1) + 1 from rfl,
        rn_succ_step (step_disc_cons k v a R O B)]
      exact phaseD k B R O (some a)

/-- Reversal phase: the accumulator is moved onto the output, which reverses it back. -/
theorem phaseR (k : ℕ) : ∀ (B O : List Bool) (v : Option Bool),
    rn k (B.length + 1) (cfgN k (k + 1) v [] O B) = some ⟨none, none, ![[], B.reverse ++ O, []]⟩
  | [], O, v => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step_rev_end k v O)]
      simp [rn]
  | a :: B, O, v => by
      rw [show (a :: B).length + 1 = (B.length + 1) + 1 from rfl,
        rn_succ_step (step_rev_push k v a O B)]
      rw [phaseR k B (a :: O) (some a)]
      simp [List.reverse_cons, List.append_assoc]

theorem initList_eq (k : ℕ) (z : List Bool) : initList (tm k) z = cfgN k 0 none z [] [] := by
  unfold initList cfgN
  congr 1
  refine funext fun (j : Fin 3) => ?_
  fin_cases j <;> simp [tm]

theorem haltList_eq (k : ℕ) (O : List Bool) :
    haltList (tm k) O = ⟨none, none, ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (j : Fin 3) => ?_
  fin_cases j <;> simp [tm]

/-- Every input is cut to its first `k` symbols by the machine in at most `|w| + 2k + 3` steps. -/
theorem gen (k : ℕ) (w : List Bool) : ∃ s, s ≤ w.length + (2 * k + 3) ∧
    rn k s (cfgN k 0 none w [] []) = some ⟨none, none, ![[], w.take k, []]⟩ := by
  obtain ⟨s1, v1, hs1, h1⟩ := phaseA k w 0 [] [] none (Nat.zero_le k)
  rw [Nat.sub_zero, List.append_nil] at h1
  have hd := phaseD k (w.take k).reverse (w.drop k) [] v1
  have hr := phaseR k (w.take k).reverse [] none
  rw [List.reverse_reverse, List.append_nil] at hr
  have h12 := rn_trans h1 hd
  refine ⟨(w.take k).reverse.length + 1 + ((w.drop k).length + 1 + s1), ?_, rn_trans h12 hr⟩
  simp only [List.length_reverse, List.length_drop, List.length_take, Nat.sub_zero] at hs1 ⊢
  omega

noncomputable def machine (k : ℕ) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) (List.take k) where
  tm := tm k
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + Polynomial.C (2 * k + 3)
  outputsFun z := by
    have hs := (gen k z).choose_spec.1
    have he := (gen k z).choose_spec.2
    have key : (fun o => o.bind (TM2.step (prog k)))^[(gen k z).choose]
        (some (initList (tm k) z)) = some (haltList (tm k) (z.take k)) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(gen k z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList (tm k)) (List.map_id z)
        | exact congrArg (fun l => some (haltList (tm k) l)) (List.map_id (z.take k))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      omega

theorem main : ∀ k : ℕ, ∃ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
    ∀ x : List Bool, T x = x.take k :=
  fun k => ⟨List.take k, ⟨machine k⟩, fun _ => rfl⟩

end MPP.Solutions.Pnp118
