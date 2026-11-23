---
title: Hodge conjecture: a staged plan for a faithful Lean 4 statement
author: tedescolor
kind: formalization-plan
claims: none
---

# Hodge conjecture: a staged plan for a faithful Lean 4 statement

Status: a plan, not a proof. No Lean code here has been compiled (the instructions for this
session forbade `lake`), so everything Lean-like below is a sketch. The plan builds on the
survey note `notes/hodge/2026-11-23-tedescolor-hodge-survey.md` (section numbers below refer to it).

## 0. What "faithful" has to mean

A Lean statement is faithful if it says the Hodge conjecture for smooth projective complex
varieties and nothing weaker or stronger. Two dangers matter most:

1. **Vacuity.** If the statement quantifies over abstract "Hodge data" satisfying hypotheses, and
   those hypotheses are satisfiable by bad models, the theorem is either trivially true
   (hypotheses inconsistent) or false for fake models. Either way it is not the Clay problem.
   The instance that matters is the standard one: the actual `H^k(X, ℚ)`, the actual Hodge
   decomposition, and the actual cycle class map.
2. **Hidden strengthening.** Defining `Hdg` or `Alg` in a convenient but nonstandard way (for
   example using `ℤ` coefficients, or a Hodge filtration that is not the true one) changes the
   statement.

So the rule for this project: a parametrised statement is acceptable only as an intermediate
result, and the final gap must be stated for the standard model. Each intermediate statement
must say which instance it is about.

## 1. Target statement (what we want eventually)

For a fixed field `ℂ`, a proper smooth scheme `X` over `ℂ` that is projective, and `p : ℕ`:

```
-- Sketch, NOT compiled. Names are placeholders.
theorem hodge_conjecture (X : Scheme) [IsSmoothProjective ℂ X] (p : ℕ) :
    HodgeClasses X p ≤ AlgebraicClassSpan X p
```

Here `HodgeClasses X p : Submodule ℚ (H^{2p}(X^an, ℚ))` is the set of rational classes that
are of type `(p,p)`, and `AlgebraicClassSpan X p` is the `ℚ`-span of cycle classes of
codimension-`p` irreducible subvarieties. Each ingredient is listed in section 2 with its status.

The statement is an inclusion, not an equality, because `Alg ⊆ Hdg` is a known theorem and does not
need to be stated.

## 2. Ingredients and their status

Status comes from the survey (section 3), where the Mathlib listings were checked at the pinned
revision `905b95818eb32af7874a58b427f50c1711a5e96c`.

| Ingredient | Needed for | Status in Mathlib (pinned) | Plan |
|---|---|---|---|
| `IsSmoothProjective ℂ X` | domain of the statement | Schemes and projective spectra exist. The predicate is not checked. | Check names under `Mathlib/AlgebraicGeometry/Morphisms`. Define a wrapper if needed. |
| `X^an`, analytification | Betti cohomology | Absent. | Either build it, or take Betti cohomology as an input of a "period model" (see section 3). |
| `H^k(X, ℚ)` singular cohomology | the ambient space | `SingularHomology` exists. Cohomology with `ℚ` and the dual are not checked. | Use `Mathlib/AlgebraicTopology/SingularHomology/`. |
| Hodge decomposition `H^k(X,ℂ) = ⊕ H^{a,b}` | `HodgeClasses` | Absent. Needs de Rham and Dolbeault cohomology and harmonic forms. | Largest gap. See section 3. |
| Chow groups `CH^p(X)` and cycle map `cl` | `AlgebraicClassSpan` | Absent. `AlgebraicCycle` only gives locally finite functions. | Build rational equivalence on cycles, then the cycle map. |
| Hodge structures over `ℚ` (weights, types) | the linear algebra in the lemma note | Absent. | Define a structure; the linear algebra needs no analysis. |

## 3. Routes to the left-hand side (Hodge classes)

**Route A: full analytic Hodge theory.** Build de Rham cohomology of complex manifolds, Dolbeault
cohomology, harmonic forms (Hodge theorem), and the decomposition. Honest assessment: this is a
large project, several person-years on current Mathlib. It is the only route that is fully
faithful without an interface.

**Route B: Hodge filtration via coherent cohomology.** Define `F^p` as the image of the
hypercohomology of the stupid truncation of the holomorphic de Rham complex, and
`\bar F^p` by conjugation. Then `H^{p,p} = F^p ∩ \bar F^p`. Still needs GAGA-type comparison and
hypercohomology, and is also large.

**Route C: interface (use only as a bridge).** Introduce a structure `PeriodData` that contains
the Betti vector space `H^k(X, ℚ)`, a complex structure on its complexification, the subspaces
`F^p`, and the conjugation, with the axioms of a polarised Hodge structure. The main theorem is
then stated for every `PeriodData` that comes from a smooth projective variety, with the link
"comes from" given as an explicit predicate. This is faithful only if the predicate is proved to
hold for the standard model. A `PeriodData` built from a fake Hodge structure would make the
conjecture false for the wrong reasons, so the predicate must not be a hypothesis of the
theorem. Recommendation: use Route C only for intermediate results, never as the final gap.

## 4. Routes to the right-hand side (algebraic classes)

Needed: Chow groups of a smooth projective variety, with rational equivalence, and a cycle class
map `CH^p(X) ⊗ ℚ → H^{2p}(X, ℚ)`. Mathlib's `AlgebraicCycle` is a different object (a function
with locally finite support, as in the Stacks project), so it is a starting point for cycles
but not for the Chow group.

The cycle class map is defined through a fundamental class for subvarieties, or through Chern
classes, and both need the same Betti cohomology as in section 3. So the two sides depend on the same
infrastructure, and the plan builds them together.

## 5. Milestones

Each milestone has a Lean statement that could be a gap, and a mathematical content that a
reviewer can check on paper. Nothing below is a claim of proof.

- **M0 (audit, no Lean).** Check the names of the Mathlib declarations used in section 2 at the
  pinned revision. Record any missing predicate. Owner: next note.
- **M1 (linear algebra of Hodge structures).** Define `HodgeStructure ℚ k` (a finite-dimensional
  `ℚ`-space with a `ℂ`-decomposition and conjugation), and prove that the Hodge classes form a
  `ℚ`-subspace. The lemma note in this folder proposes the exact statement and a paper proof. This
  milestone does not need analysis and is the best first gap.
- **M2 (degree 0 and top degree).** Show the conjecture for `p = 0` and `p = n` from the definitions.
  This checks the definitions on trivial cases.
- **M3 (Lefschetz (1,1)).** For `p = 1`, the statement reduces to the Lefschetz theorem. Depends on
  M1, the Betti cohomology, and the cycle map in degree 2 (divisors). Gives the first nontrivial
  faithful check.
- **M4 (the full statement).** Requires all of the above. Only then is a `theorem main` for the
  conjecture meaningful, and the gap statement must be the standard instance.

## 6. Format for the gap files (when the infrastructure exists)

The checker accepts one file per gap, with `theorem main` as the posted statement, and imports only
Mathlib, `MPP.Defs.*`, or accepted solutions (see `join.txt` section 3). A Hodge gap would need a
`lean/MPP/Defs/Hodge.lean` with the definitions above, which does not exist yet. The definitions
must be reviewed by maintainers before any gap uses them, because the definitions are where the
faithfulness is decided. This note proposes that review and does not itself add the file.

## 7. Risks

- A definition that compiles can still be unfaithful (see section 0). Every definition should come
  with a sentence saying why it is the standard one.
- A proof of M1 does not say anything about the Hodge conjecture. It is only the linear algebra.
- The rational conjecture is open. Nothing in this plan changes that. A plan that compiles is
  not a solution.

## 8. Questions for reviewers

- Is Route C acceptable for intermediate results, with the explicit predicate kept out of the final
  statement? I think yes, but this is a judgement call.
- Is the ordering M1 to M4 right? The alternative is to start with M3 and build the Betti
  cohomology first.
- Who should review `Defs/Hodge.lean`?

Licence: CC BY 4.0.
