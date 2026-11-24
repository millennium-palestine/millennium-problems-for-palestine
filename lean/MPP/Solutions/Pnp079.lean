import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp045
import MPP.Solutions.Pnp072

namespace MPP.Solutions.Pnp079

open MPP.PvsNP Turing

/-- Padded encoding of a witness of length at most `N` as a string of length `N + 1`:
leading zeros, a marker `true`, then the witness. Lex order on these strings is
shortlex order on the witnesses. -/
def enc (N : ℕ) (w : List Bool) : List Bool :=
  List.replicate (N - w.length) false ++ true :: w

theorem enc_length (N : ℕ) (w : List Bool) (h : w.length ≤ N) :
    (enc N w).length = N + 1 := by
  unfold enc
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

theorem enc_succ (N : ℕ) (w : List Bool) (h : w.length ≤ N) :
    enc (N + 1) w = false :: enc N w := by
  unfold enc
  rw [show N + 1 - w.length = (N - w.length) + 1 by omega, List.replicate_succ]
  rfl

theorem dropWhile_enc_aux (k : ℕ) (w : List Bool) :
    (List.replicate k false ++ true :: w).dropWhile (fun b => !b) = true :: w := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem dec_enc (N : ℕ) (w : List Bool) :
    ((enc N w).dropWhile fun b => !b).tail = w := by
  unfold enc
  rw [dropWhile_enc_aux]
  rfl

theorem replicate_false_lt (b : ℕ) (A B : List Bool) (h : A < B) :
    List.replicate b false ++ A < List.replicate b false ++ B := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append]
    exact List.cons_lt_cons_iff.2 (Or.inr ⟨by simp, ih⟩)

/-- A padded string containing the marker is the encoding of the witness it decodes to. -/
theorem enc_dec (u : List Bool) : ∀ N : ℕ, u.length = N + 1 → true ∈ u →
    u = enc N ((u.dropWhile fun b => !b).tail) := by
  induction u with
  | nil => intro N _ h; simp at h
  | cons c us ih =>
    intro N hlen hT
    cases c
    · have hT' : true ∈ us := by simpa using hT
      have hus : us.length = N := by simp only [List.length_cons] at hlen; omega
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
        cases N with
        | zero => simp at hus; simp [hus] at hT'
        | succ N' => exact ⟨N', rfl⟩
      have ih' := ih N' hus hT'
      have hw : ((us.dropWhile fun b => !b).tail).length ≤ N' := by
        have := List.length_dropWhile_le (fun b => !b) us
        simp only [List.length_tail]
        omega
      have hd : (false :: us).dropWhile (fun b => !b) = us.dropWhile (fun b => !b) := by simp
      rw [hd, enc_succ N' _ hw]
      congr 1
    · have hd : (true :: us).dropWhile (fun b => !b) = true :: us := by simp
      have hus : us.length = N := by simp only [List.length_cons] at hlen; omega
      rw [hd, List.tail_cons]
      unfold enc
      rw [hus, Nat.sub_self]
      rfl

theorem enc_lt (N : ℕ) (w w' : List Bool) (hw : w.length ≤ N) (hw' : w'.length ≤ N)
    (h : w.length < w'.length ∨ (w.length = w'.length ∧ w < w')) :
    enc N w < enc N w' := by
  rcases h with h | ⟨h, hlt⟩
  · -- the shorter witness has strictly more leading zeros, so its encoding starts with `false`
    obtain ⟨k, hk⟩ : ∃ k, N - w.length = (N - w'.length) + k + 1 :=
      ⟨N - w.length - (N - w'.length) - 1, by omega⟩
    unfold enc
    rw [hk, show (N - w'.length) + k + 1 = (N - w'.length) + (k + 1) by omega,
      List.replicate_add, List.append_assoc]
    apply replicate_false_lt
    rw [List.replicate_succ]
    exact List.cons_lt_cons_iff.2 (Or.inl (by decide))
  · unfold enc
    rw [← h]
    exact replicate_false_lt _ _ _ (List.cons_lt_cons_iff.2 (Or.inr ⟨by simp, hlt⟩))

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V → PEqualsNP →
    ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ V (pair x w) = true) →
        (f x).length ≤ p.eval x.length ∧ V (pair x (f x)) = true ∧
        ∀ w : List Bool, w.length ≤ p.eval x.length → V (pair x w) = true →
          ¬ (w.length < (f x).length ∨ (w.length = (f x).length ∧ w < f x)) := by
  intro V p hV hPNP
  obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨g, ⟨hg⟩, hgx⟩ := MPP.Solutions.Pnp045.main
  obtain ⟨r, ⟨hr⟩, hrz⟩ :=
    MPP.Solutions.Pnp026.main d (g ∘ e) ⟨hd⟩ (MPP.Solutions.Pnp006.main he hg)
  -- the verifier that reads the padded witness: `V` applied to the decoded pair
  have hr_enc : ∀ x u, r (pair x u) = pair x (g u) := by
    intro x u
    simp [hrz, hdx, hex]
  have hV2 : InP (fun z => V (r z)) := MPP.Solutions.Pnp008.main V r hV hr
  obtain ⟨f2, ⟨hf2⟩, hf2x⟩ := MPP.Solutions.Pnp072.main (fun z => V (r z)) (p + 1) hV2 hPNP
  refine ⟨fun x => g (f2 x), MPP.Solutions.Pnp006.main hf2 hg, fun x hw => ?_⟩
  obtain ⟨w0, hw0, hw0V⟩ := hw
  have hA : ∃ w : List Bool, w.length = (p + 1).eval x.length ∧
      (fun z => V (r z)) (pair x w) = true := by
    refine ⟨enc (p.eval x.length) w0, ?_, ?_⟩
    · rw [enc_length _ _ hw0, Polynomial.eval_add, Polynomial.eval_one]
    · show V (r (pair x (enc (p.eval x.length) w0))) = true
      rw [hr_enc, hgx, dec_enc, hw0V]
  obtain ⟨hlen, hacc, hmin⟩ := hf2x x hA
  have hN : (f2 x).length = p.eval x.length + 1 := by
    rw [hlen, Polynomial.eval_add, Polynomial.eval_one]
  have hgle : (g (f2 x)).length ≤ p.eval x.length := by
    rw [hgx, List.length_tail]
    have := List.length_dropWhile_le (fun b => !b) (f2 x)
    omega
  refine ⟨hgle, ?_, fun w hwlen hwV hcmp => ?_⟩
  · have h := hacc
    rw [hr_enc] at h
    exact h
  · by_cases hT : true ∈ f2 x
    · -- the greedy-shortlex string is exactly the padded encoding of its decoding
      have hu : f2 x = enc (p.eval x.length) (g (f2 x)) := by
        rw [hgx]
        exact enc_dec (f2 x) _ hN hT
      have hlt := enc_lt (p.eval x.length) w (g (f2 x)) hwlen hgle hcmp
      have hlen' : (enc (p.eval x.length) w).length = (p + 1).eval x.length := by
        rw [enc_length _ _ hwlen, Polynomial.eval_add, Polynomial.eval_one]
      have hmw : (fun z => V (r z)) (pair x (enc (p.eval x.length) w)) = true := by
        show V (r (pair x (enc (p.eval x.length) w))) = true
        rw [hr_enc, hgx, dec_enc, hwV]
      exact hmin _ hlen' hmw (by rw [hu]; exact hlt)
    · have hz : g (f2 x) = [] := by
        rw [hgx]
        have hnil : (f2 x).dropWhile (fun b => !b) = [] := by
          rw [List.dropWhile_eq_nil_iff]
          intro b hb
          cases b
          · simp
          · exact absurd hb hT
        rw [hnil]
        rfl
      simp [hz] at hcmp

end MPP.Solutions.Pnp079
