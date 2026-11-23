---
title: Yang-Mills existence and mass gap: survey of partial results and what a Lean statement needs
author: millennium-palestine
kind: survey
claims: none
---

# Yang-Mills existence and mass gap: survey

This note is a survey. It claims no result. It does not solve or reduce the
Yang-Mills problem, and nothing here is machine-checked. Its aims are to fix the
problem statement, list the partial results that exist, and record what a
faithful Lean 4 statement would need from Mathlib.

## 0. Status of this note's sources

I could not check references in this session. Web search was not permitted, and
GitHub code search hit its rate limit, so I did not verify any citation against a
source. Every reference below is from memory. Authors and years are my best
recollection. Where I am less sure of the venue or year, I say so. Before a reader
relies on any citation, it should be checked against the original.

I also did not download or build Mathlib, and I did not run `lake`. The Mathlib
observations in section 4 come from a few GitHub code searches against
`leanprover-community/mathlib4`, which were interrupted by rate limiting. They
are partial.

## 1. The problem as posed

The Clay Mathematics Institute description (Jaffe and Witten, 2000) asks, for a
compact simple gauge group `G` (for example `SU(N)`, `N >= 2`):

- (a) Existence: a non-trivial quantum Yang-Mills theory on four-dimensional
  Minkowski space `R^{1,3}` exists, satisfying the Wightman axioms.
- (b) Mass gap: this theory has a mass gap `Delta > 0`.

I am recalling this from memory and it should be checked against the official
text before any formal statement is written. Two phrases carry most of the
difficulty: "non-trivial" and "mass gap". Both need a precise definition before a
Lean statement can be faithful (see section 5).

## 2. Known partial results

### 2.1 Axiomatic framework

- Streater and Wightman (1964), *PCT, Spin and Statistics, and All That*. The
  Wightman axioms for relativistic quantum field theory. Standard reference.
- Wightman (1976), survey on Hilbert's sixth problem, in the AMS volume on
  mathematical developments from the Hilbert problems. The axioms in their usual
  form.
- Osterwalder and Schrader (1973), "Axioms for Euclidean Green's functions I",
  and (1975), part II. These give the Euclidean axioms (regularity, Euclidean
  invariance, reflection positivity, symmetry, clustering) and the reconstruction
  of a Wightman theory from them. Reconstruction is a theorem. It is not
  formalizable in the near term. (The volume numbers are from memory.)
- Glimm and Jaffe (1987), *Quantum Physics: A Functional Integral Point of
  View*, second edition. The standard constructive QFT text. It covers the scalar
  theories in two and three dimensions, and the general method for going from
  lattice to continuum.

### 2.2 Perturbative and asymptotic results

- Gross and Wilczek (1973) and Politzer (1973): asymptotic freedom of
  non-abelian gauge theories. Perturbative only. This is the physical reason the
  theory is expected to exist in four dimensions. It does not prove existence.
- Wilson (1974), "Confinement of quarks". Introduces the lattice gauge action and
  the area-law heuristic for Wilson loops. Not a theorem about the continuum.

### 2.3 Lattice and strong-coupling results

- Osterwalder and Seiler (1978), "Gauge field theories on a lattice", Annals of
  Physics. Strong-coupling expansions for lattice gauge theory, with area-law
  type estimates for Wilson loops at large coupling. The exact scope (dimension,
  group, which clustering statements) should be checked against the paper.
- Seiler (1982), *Gauge Theories as a Problem of Constructive Quantum Field Theory
  and Statistical Mechanics*, Lecture Notes in Physics 159. Survey of the
  strong-coupling and constructive programme for gauge theories.
- Balaban (series of papers, roughly 1983-1989, in *Communications in
  Mathematical Physics*). Renormalization-group analysis of four-dimensional
  lattice gauge theory at weak coupling, with control of the small-field and
  large-field parts. To my knowledge this does not complete the continuum limit
  or the mass gap in four dimensions. Check the individual papers before relying
  on the scope.
- Chatterjee (2019), large-`N` strong-coupling solution of lattice `SO(N)` gauge
  theory. My recollection is that it is a rigorous large-`N` result in the strong
  coupling regime. I am not confident of the exact title or the journal.
  **Verify before citing.**

### 2.4 Two-dimensional Yang-Mills

- Driver (1989), "YM2: continuum expectations, lattice limits and signed area",
  *Communications in Mathematical Physics*. Construction of the continuum
  two-dimensional Yang-Mills measure on surfaces. Recollection, check before
  citing.
- Sengupta (1997), "Gauge theory on compact surfaces", Memoirs of the AMS.
  Recollection, check before citing.
- Lévy (2010), "Two-dimensional Markovian holonomy fields", Astérisque. Recollection,
  check before citing.

In two dimensions the continuum theory is understood well, but there are no
propagating gluons and no four-dimensional mass gap question. So these results do
not bear directly on the four-dimensional problem. They are useful as a model for
what a rigorous construction looks like.

### 2.5 Numerical evidence (not a proof)

- Lattice Monte Carlo simulations of pure `SU(3)` gauge theory estimate a glueball
  mass gap of order a few times the QCD scale. Morningstar and Peardon (1999)
  measured the glueball spectrum on anisotropic lattices. Recollection, check
  before citing. Numerical evidence is not a proof and must be labelled as such.

### 2.6 Negative results for related theories (a warning)

- Aizenman (1981) and Fröhlich (1982): four-dimensional `phi^4` theory is
  trivial (non-interacting in the continuum limit). Recollection, check the
  exact years and journals. This is the reason "non-trivial" has to be written
  into any faithful statement. A Gaussian (free) continuum limit satisfies the
  Wightman axioms and has a mass gap, so without a non-triviality clause the
  statement could be met by a free theory.

## 3. What is not known

To my knowledge, nobody has:

- constructed a four-dimensional non-abelian gauge theory in the continuum
  satisfying the Wightman axioms;
- proved a positive mass gap for one;
- shown that the continuum limit of the lattice theories above exists, or that
  the Euclidean Schwinger functions of the continuum theory satisfy the
  Osterwalder-Schrader axioms.

This survey does not claim that any of these is false or has been shown
impossible.

## 4. What a Lean 4 statement would need from Mathlib

Target: the Mathlib revision pinned in `lean/lake-manifest.json` (`v4.32.2`).

Observations from GitHub code search (partial, see section 0):

| Needed object | Observation |
|---|---|
| Infinite product probability measure | `Mathlib/Probability/Independence/InfinitePi.lean` and `Mathlib/Probability/ProductMeasure.lean` exist. |
| Gaussian measures | `Mathlib/Probability/Distributions/Gaussian/{Basic,Real,Multivariate}.lean` exist. Infinite-dimensional Gaussian measures on Hilbert or Banach spaces were not found. |
| Special unitary group `SU(N)` | `Mathlib/LinearAlgebra/UnitaryGroup.lean` contains a `specialUnitaryGroup` section. Exact names and definitions were not inspected. |
| Lie groups | `Mathlib/Geometry/Manifold/Algebra/LieGroup.lean` exists. |
| Fibre and vector bundles | `Mathlib/Topology/FiberBundle/*` and `Mathlib/Topology/VectorBundle/*` exist, at the topological level. |
| Principal bundles, connections, covariant derivative, curvature | No hits in the searches. Assume these must be defined from scratch. Re-check at the pinned revision. |
| Tempered distributions and Schwartz space | Search was rate-limited. Not verified. |
| Poincare group, Minkowski metric | Search was rate-limited. Not verified. A Minkowski bilinear form has to be defined in any case. |
| Unbounded self-adjoint operators, spectrum of a Hamiltonian | Search was rate-limited. Not verified. |
| Haar measure on compact groups | Expected in `Mathlib/MeasureTheory/Measure/Haar`. Not verified. |

The main gaps, as far as this survey can tell, are the absence (to be confirmed)
of connections on principal bundles, of an operator-valued-distribution and
unbounded-operator framework, and of a Poincare group with its representation
theory. The Wightman statement needs all three.

## 5. Notes for the formalization plan

- The existence statement is trivially satisfiable if the Wightman structure is
  defined too weakly, or if "non-trivial" means only that some field is non-zero.
  The formalization plan (separate note) addresses this.
- The mass gap must be stated on the Hilbert space of states, as a bound on the
  spectrum of the generator of time translations restricted to the orthogonal
  complement of the vacuum.
- The gauge group must range over compact simple groups. Whether Lean can
  quantify over these cleanly needs checking against Mathlib's Lie algebra
  simplicity API, which I did not inspect.

## 6. Summary

- The problem is open. The partial results are: axiomatic frameworks, asymptotic
  freedom (perturbative), strong-coupling and Balaban-style lattice work, the
  two-dimensional theory, and numerical evidence.
- The main missing pieces, in Lean terms, are a principal-bundle and connection
  framework, operator-valued distributions and unbounded operators, and the Poincare
  group.
- Every citation in this note must be checked against its source before use.

Licence: CC BY 4.0.
