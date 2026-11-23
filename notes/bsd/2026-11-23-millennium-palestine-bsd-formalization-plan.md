---
title: Birch and Swinnerton-Dyer (rank part): a formalization plan for Lean 4 with Mathlib
author: millennium-palestine
kind: formalization-plan
claims: none (a plan and a candidate statement; it proves nothing, and the Lean sketch below was not compiled)
---

# Scope and limits

This plan covers the rank part of the BSD conjecture for elliptic curves over Q, in Clay's form: rank E(Q) = ord_{s=1} L(E, s). It proposes a Lean 4 statement, lists what Mathlib lacks, and gives a staged plan.

Limits of this work:

- Nothing was compiled. No `lake` run and no Mathlib download, by instruction. The Lean code below is a sketch: names and signatures must be checked against a current Mathlib before anyone relies on them.
- Mathlib facts come from reading the default branch through the GitHub API on 2026-11-23. Absence claims are weak; see the companion survey note in this folder for the full inventory.
- The conjecture is open. A faithful statement is a target, not a result. Any gap below marked "open" stays open.

# 1. Target statement (informal)

For every elliptic curve E over Q, the rank of the abelian group E(Q) equals the order of vanishing at s = 1 of the analytic continuation of L(E, s), where L(E, s) = ∏_p L_p(E, s) is the Hasse–Weil L-function.

# 2. Design decisions

**(a) The curve.** Use an integral Weierstrass model E₀ over ℤ, and require it to be minimal. The minimality requirement is not optional: a non-minimal model reduces to a cusp at some prime where the minimal model has good or multiplicative reduction, so the a_p would be wrong. Minimality is not in Mathlib (not found), so it must be defined. Every E/Q has a global minimal model (a standard fact; see Silverman, *The Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics 106, Springer, 1986, whose DOI Crossref confirmed; I did not check the statement in the book). Quantifying over minimal models covers all curves only once that existence fact is proved, so it must be a companion lemma, not an assumption.

**(b) The local factors.** Define, for each prime p,

  a_p := p − #{(x, y) ∈ 𝔽_p² : the Weierstrass equation holds}.

This is the same as p + 1 − #Ẽ(𝔽_p), where Ẽ counts projective points including the point at infinity. It gives the standard values:

- good reduction: a_p = p + 1 − #E(𝔽_p), the usual formula;
- split multiplicative (node with split tangents): a_p = 1;
- non-split multiplicative: a_p = −1;
- additive (cusp): a_p = 0.

I checked these three bad-reduction cases by counting smooth points and the singular point. The check is on paper only; a Lean proof would be a real lemma.

**(c) The coefficients.** Extend a_p to all n ≥ 1 as usual. For good p, a_{p^{k+2}} = a_p a_{p^{k+1}} − p a_{p^k}. For bad p, a_{p^k} = a_p^k. Set a_n = ∏_{p | n} a_{p^{v_p(n)}}, so the function is multiplicative. Use `Nat.factorization` for the product.

**(d) The L-function.** Let L(E, s) be the Dirichlet series with coefficients a_n, so `LSeries (fun n => (a n : ℂ)) s`, which converges absolutely for Re s > 3/2 (Hasse's bound |a_p| ≤ 2√p; not in Mathlib, not found).

**(e) Analytic continuation and the order at 1.** Use the universal form:

  for every entire Λ : ℂ → ℂ that agrees with the series on Re s > 3/2, there is r : ℕ with rank E(Q) = r and analyticOrderAt Λ 1 = r.

Two reasons for this shape. It avoids a meromorphic order on a non-entire function, since L(E, s) is entire by modularity. And it states the rank as a natural number, which also asserts finite generation (Mordell–Weil). Pitfall: the universal form is vacuous if no entire continuation exists. Modularity gives one, so the statement is not vacuous, but the existence must be proved as a companion statement, not assumed.

**(f) The rank.** Use `Module.rank ℤ (E(Q))`, which is a cardinal and is the right invariant even when the group is not known to be finitely generated (torsion contributes nothing). Pitfall: casting a cardinal to ℕ∞ is not available, so the r : ℕ existential is the honest form.

# 3. Candidate Lean sketch (not compiled)

```lean
import Mathlib

namespace MPP.Defs.BSD

open WeierstrassCurve

/-- Points of the reduction mod p in the affine plane. -/
noncomputable def affineCount (E : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Nat.card {xy : ZMod p × ZMod p //
    (E.map (Int.castRingHom (ZMod p))).Equation xy.1 xy.2}

/-- a_p = p - #affine points of the reduction. Needs checking against
    the current signatures of `WeierstrassCurve.map` and `Equation`. -/
noncomputable def ap (E : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] : ℤ :=
  (p : ℤ) - (affineCount E p : ℤ)

-- Coefficients a_{p^k}: good primes via the Hecke recursion,
-- bad primes via a_p^k. Definition omitted here; see plan section 2(c).
-- noncomputable def primePowCoeff (E : WeierstrassCurve ℤ) (p k : ℕ) : ℤ := ...
-- noncomputable def hasseCoeff (E : WeierstrassCurve ℤ) (n : ℕ) : ℤ := ...

-- Minimality is not in Mathlib and must be defined. Placeholder:
-- def IsMinimal (E : WeierstrassCurve ℤ) : Prop := ...

/-- Candidate statement. Not compiled, and not proved. -/
-- theorem bsd_rank_part (E : WeierstrassCurve ℤ) (hmin : IsMinimal E)
--     [haveI : (E.map (algebraMap ℤ ℚ)).IsElliptic := ...] :
--     ∀ Λ : ℂ → ℂ, Differentiable ℂ Λ →
--       (∀ s : ℂ, 3 / 2 < s.re → Λ s = LSeries (fun n => (hasseCoeff E n : ℂ)) s) →
--       ∃ r : ℕ, Module.rank ℤ (E.map (algebraMap ℤ ℚ)).Point = r ∧
--         analyticOrderAt Λ 1 = (r : ℕ∞)

end MPP.Defs.BSD
```

Points to check in a real build:

- The point group of the curve over Q needs the `IsElliptic` instance; this requires Δ ≠ 0 in Q, and the instance must be supplied where the statement uses it.
- `WeierstrassCurve.Point` and the `Projective` versus `Affine` choice for E(Q) must be fixed; the rank is the same for both.
- `Differentiable` on C is used for "entire"; check whether `analyticOrderAt` wants `AnalyticAt` at 1, and whether a Mathlib lemma converts differentiability to analyticity.

# 4. Mathlib inventory and gaps

Present (default branch, 2026-11-23): `WeierstrassCurve`, `WeierstrassCurve.IsElliptic`, the point groups `WeierstrassCurve.Projective.Point.instAddCommGroup` and `WeierstrassCurve.Affine.Point.instAddCommGroup`, `WeierstrassCurve.Equation`, naive heights and their finiteness, the descent criterion `AddGroup.fg_of_descent`, `LSeries`, `analyticOrderAt : ℕ∞`, `meromorphicOrderAt`, modular forms, cusp forms, and an L-function of a modular form.

Missing, each a real gap:

1. **Mordell–Weil** (finite generation of E(Q)). Needed for the existential r. Plausible route: weak Mordell–Weil (finiteness of E(Q)/2E(Q)) by 2-descent, plus the present descent criterion and the height finiteness. Large but concrete.
2. **Hecke operators and newforms.** Needed to show L(E, s) continues to an entire function with the expected functional equation. Absent in the text search.
3. **Modularity** (Wiles; Taylor–Wiles; Breuil–Conrad–Diamond–Taylor). Needed for the continuation. This is the largest gap: a formalization of modularity would be a major project.
4. **Minimal models and Tate's algorithm / Kodaira types.** Needed for the definition in 2(a) and for the classification in 2(b). Absent in the text search.
5. **Hasse's bound** |a_p| ≤ 2√p. Needed for the convergence region. Absent.

# 5. Staged plan

- **Stage 0 (this note).** Fix the candidate statement and the design decisions. Ask a number theorist or a Lean user to review the definitions, especially the minimality definition and the bad-reduction convention.
- **Stage 1 (definitions).** Compile the definitions of `affineCount`, `ap`, `primePowCoeff` and `hasseCoeff`. Check multiplicativity for coprime arguments. Check the values of a_p on explicit examples (for example, one curve of each reduction type), by direct computation rather than by a Tate-algorithm proof.
- **Stage 2 (convergence).** Prove the Hasse bound, if it is not in a current Mathlib, and deduce absolute convergence for Re s > 3/2.
- **Stage 3 (continuation).** This is the obstacle. Options: (i) formalize modularity, far beyond current reach; (ii) state the theorem conditionally on the modularity of E, clearly labelled as conditional, and keep the unconditional statement as the target. Option (ii) is a labelled partial result, not BSD.
- **Stage 4 (rank side).** Prove finite generation (Mordell–Weil) for E(Q). Only then is the existential r meaningful as a theorem rather than a hypothesis.
- **Stage 5 (the statement itself).** The target equality is BSD for E/Q. Its proof is open.

# 6. Faithfulness checklist for any future version

- The universal form over Λ is non-vacuous only with the continuation proved as a companion.
- The curve is minimal at every prime, and the definition is checked.
- The rank is stated as a natural number, which asserts finiteness; that is the intended content.
- The order is `analyticOrderAt` at s = 1 on an entire function, not a meromorphic order on an arbitrary function.
- Any conditional variant names its hypothesis in the theorem's name and in the note's title.

# 7. Honesty note

This plan does not claim that BSD is solved or that any step is proved. The Lean sketch is unchecked. The mathematics above is from the literature as I recall it, flagged as such in the survey note, and needs review.
