---
title: Yang-Mills: a staged plan to state the problem faithfully in Lean 4 with Mathlib
author: millennium-palestine
kind: formalization-plan
claims: none
---

# Yang-Mills: staged formalization plan

This is a plan. It claims no theorem and proves nothing. The Lean snippets below
are sketches. None of them has been elaborated, and none is checked. Their only
purpose is to make the design questions concrete. The companion survey note
(`notes/yang-mills/2026-11-23-millennium-palestine-ym-survey.md`) gives the
background, and its caveats about references and Mathlib apply here too.

## 1. The goal, and why a single statement is not enough

The target is a Lean statement of the Clay problem: for compact simple `G`, a
non-trivial Wightman quantum Yang-Mills theory on `R^{1,3}` exists, with a mass
gap `Delta > 0`.

A single definition of that statement is the hard part. The construction itself
is open. So the plan is staged. Each stage gives a definition that can be reviewed,
and some stages give small lemmas that can be checked. The top-level statement is
the last stage.

## 2. Design decisions to settle first

These decisions shape everything below. Each needs review by a specialist before
any Lean code is written.

1. **Which gauge groups.** Options: (i) a fixed `SU(N)`, (ii) a class of
   compact simple Lie groups given by their Lie algebras. Option (ii) is faithful
   to the Clay wording. It requires a clean "compact simple" predicate. Check
   whether Mathlib has a usable notion of simple Lie algebra (`LieAlgebra.IsSimple`
   or similar) and of compactness for the group. The plan recommends starting
   with `SU(N)` and generalising later.
2. **Euclidean or Minkowski.** The Wightman axioms are Minkowskian. The
   construction is usually Euclidean. A faithful statement must mention Minkowski
   space and the Hilbert space of states. The Euclidean stage is used only as an
   intermediate definition, linked by the Osterwalder-Schrader reconstruction.
3. **How to define "non-trivial".** This is the main risk. See section 5.
4. **How to define "mass gap".** Recommended form: let `H` be the generator of
   time translations on the Hilbert space `V` of the theory, `Omega` the vacuum,
   and `V_0 = Omega^perp`. A mass gap is `Delta > 0` with `spec(H|_{V_0}) subset
   [Delta, infinity)`. This needs unbounded self-adjoint operators and their
   spectra, which Mathlib may not have in usable form (see section 4).

## 3. Staged milestones

Each stage lists what it adds and what it needs from Mathlib. Stage names are
suggestions for future gap or definition ids. Nothing is claimed or assigned.

### Stage 0: finite lattice, fully finite-dimensional

Object: a finite lattice `Lambda` (a finite box in `Z^d`), with `SU(N)` link
variables. Wilson action `S_beta(U) = beta * sum over plaquettes p of (1 - Re tr U_p / N)`.

Candidate lemma (checkable in principle, a good first task):

```lean
-- Sketch, not elaborated.
-- The Wilson action is invariant under lattice gauge transformations.
theorem wilson_action_gauge_invariant
    (Λ : Finset (Fin d → ℤ)) (N β : ℝ) (g : Λ → SU N) (U : Links Λ) :
    wilsonAction β (gaugeTransform g U) = wilsonAction β U
```

Mathlib needs: `SU(N)` as a group (`Matrix.specialUnitaryGroup`, present
according to a partial search), trace, real part. Expected but unverified: a
Haar measure on the compact group.

Candidate lemma two: the partition function `Z_Lambda = integral over the finite
product of exp(-S_beta)` with respect to Haar measure is strictly positive. Needs
Haar measure and integration of positive functions.

### Stage 1: infinite lattice limit

Object: consistent family of finite-volume measures, with the infinite-volume
measure as a projective limit. Candidate tools: the infinite product measure
(`Mathlib/Probability/Independence/InfinitePi.lean`, present) and a projective
limit construction (existence in Mathlib unverified).

Output: a probability measure on configurations on the infinite lattice, for each
`beta`. Still no continuum limit.

### Stage 2: Euclidean Schwinger functions and the Osterwalder-Schrader axioms

Object: a structure `OSTheory` with fields for the Euclidean correlation functions
(Schwinger functions) and the axioms: regularity, Euclidean invariance,
reflection positivity, symmetry, clustering.

```lean
-- Sketch only. Field names and types are placeholders.
structure OSTheory (G : Type*) where
  schwinger : (n : ℕ) → (Fin n → EuclideanSpace ℝ (Fin 4)) → ℂ
  euclidean_invariant : ...
  reflection_positive : ...
  regular : ...
  clustering : ...
```

Needs: `EuclideanSpace` (present), Schwartz space or test functions (unverified).

### Stage 3: Wightman structure

Object: `WightmanTheory`, with a Hilbert space `V`, a unitary representation of
the Poincare group `P` on `V` with positive-energy spectrum condition, a vacuum
`Omega` invariant under `P`, and operator-valued distributions `phi_i` on Minkowski
space with domain conditions and locality.

Hard part: operator-valued distributions need test functions (Schwartz space,
unverified) and unbounded operators on `V` (unverified). The Poincare group and its
unitary representations are probably not in Mathlib (search rate-limited).

### Stage 4: the Clay statement

```lean
-- Sketch only. Not a definition the project should adopt yet.
def HasMassGap (W : WightmanTheory G) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ spectrum_of_H_on_vacuum_complement W ⊆ Set.Ici Δ

theorem clay_yang_mills (G : Type*) [CompactSimpleGroup G] :
    ∃ W : WightmanTheory G, IsNonTrivial W ∧ HasMassGap W := by
  sorry  -- open problem; must NOT be attempted as a proof without a new idea
```

Writing the theorem is allowed as a statement. The plan's point is that it must
not become a proof attempt disguised as a formalization.

## 4. Mathlib: what is needed and what is missing

Observations from partial GitHub code searches at the pinned revision
(`lean/lake-manifest.json`, Mathlib `v4.32.2`). Re-check all of this before
relying on it.

| Needed | Status |
|---|---|
| `SU(N)` and unitary groups | Present (`LinearAlgebra/UnitaryGroup.lean`). Exact API not inspected. |
| Lie groups | Present (`Geometry/Manifold/Algebra/LieGroup.lean`). |
| Infinite product measures | Present (`Probability/Independence/InfinitePi.lean`). |
| Gaussian measures | Present in finite dimension. Infinite-dimensional not found. |
| Principal bundles, connections, curvature, covariant derivative | Not found. Must be defined. |
| Tempered distributions, Schwartz space | Not verified (search rate-limited). |
| Poincare group, Minkowski form | Not verified. Assume to be defined. |
| Unbounded self-adjoint operators, spectrum | Not verified. |
| Haar measure on compact groups | Expected. Not verified. |

Recommendation: before writing any Lean, someone with Mathlib access should
inspect these entries at the pinned revision. The check is cheap and changes the
plan if the answers differ.

## 5. The main risk: a vacuous or trivially satisfiable statement

A faithful statement must rule out easy answers:

- **Free theory.** A Gaussian theory with no self-interaction satisfies many of
  the axioms and has a mass gap. "Non-trivial" must exclude it. A possible
  formulation is: the theory is not Gaussian, for example its connected
  three-point Schwinger function of the gauge field is non-zero. This needs a
  specialist. Four-dimensional `phi^4` shows why this matters: that theory is
  trivial in the continuum, so a non-triviality clause has to be stated carefully.
- **Empty Hilbert space or degenerate vacuum.** The mass gap should be stated on
  the complement of the vacuum, so a one-dimensional Hilbert space cannot satisfy
  it vacuously.
- **Weak axioms.** If the locality, spectrum or covariance conditions are too
  weak, the existence statement says nothing. Each field of the structure needs a
  justification against the published axioms (Streater-Wightman 1964; Wightman 1976).
- **Mass gap formulated on the wrong space.** A bound on the whole spectrum is
  always false (the vacuum sits at zero energy). The complement of the vacuum must
  be used.

Any reviewer should look first at sections 2.3 and 5. The plan is only as good as
those two definitions.

## 6. Suggested review questions

For a reviewer with a background in mathematical physics:

1. Is the Wightman structure in stage 3 equivalent, in its consequences, to the
   published axioms, with no weakening?
2. Is "non-trivial" stated in a way that excludes Gaussian theories and is
   consistent with what is expected physically?
3. Is the mass-gap definition in section 2.4 the right one?
4. Does the "compact simple" class in section 2.1 match the Clay wording?

## 7. What this plan does not do

- It does not claim that any stage will be completed.
- It does not claim that the top-level statement is true, or that it is false.
- It does not propose a proof of the mass gap or of existence.
- It does not give a Lean definition that the project should adopt. Definitions
  of this kind belong in `lean/MPP/Defs/` and need maintainer review.

Licence: CC BY 4.0.
