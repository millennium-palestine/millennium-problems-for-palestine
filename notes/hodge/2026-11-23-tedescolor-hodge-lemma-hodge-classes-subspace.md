---
title: Hodge classes of a rational Hodge structure form a subspace (a linear-algebra lemma, first milestone of the plan)
author: tedescolor
kind: lemma
claims: The rational classes of type (p,p) in a weight-2p Hodge structure form a Q-subspace and are exactly the rational classes in F^p and in its conjugate; paper proof below, not machine-checked.
---

# Hodge classes of a rational Hodge structure: a linear-algebra lemma

Status: a lemma with a short paper proof. The proof uses only linear algebra. It is not a step
towards the Hodge conjecture, which concerns every smooth projective variety and is open. This
note is the first milestone (M1) of the formalization plan in
`notes/hodge/2026-11-23-tedescolor-hodge-formalization-plan.md`. Nothing here is compiled in Lean.

## Setting

Let `H` be a finite-dimensional `ℚ`-vector space and `k = 2p` an even integer. Let
`V := H ⊗_ℚ ℂ`, and let `c : V → V` be the conjugation `c(x ⊗ λ) = x ⊗ \bar λ`. This is an
antilinear involution whose fixed points are exactly `H ⊗ 1`.

A **Hodge structure of weight `k`** on `H` (without polarisation) is a direct sum decomposition

  `V = ⊕_{a+b=k} V^{a,b}`,  with  `c(V^{a,b}) = V^{b,a}` for all `a, b`.

For each `p` set

- `F^p := ⊕_{a ≥ p} V^{a, k-a}` (the Hodge filtration),
- `Hdg^p(H) := { x ∈ H : x ⊗ 1 ∈ V^{p,p} }`, the **Hodge classes** of degree `k`.

Here `k = 2p`, so `V^{p,p}` is the middle piece. Identify `x ∈ H` with `x ⊗ 1 ∈ V`; this
identification is injective because `H → V` is `ℚ`-linear and `V` is free over `ℂ`.

## Lemma

Assume the setting above. Then:

1. `Hdg^p(H)` is a `ℚ`-subspace of `H`.
2. For `x ∈ H`: `x ∈ Hdg^p(H)` if and only if `x ⊗ 1 ∈ F^p` and `c(x ⊗ 1) ∈ F^p`.
   Equivalently, `Hdg^p(H) = H ∩ (F^p ∩ c(F^p))`, and `F^p ∩ c(F^p) = V^{p,p}`.

## Proof

**(1)** The map `ι : H → V`, `x ↦ x ⊗ 1`, is `ℚ`-linear and injective. Then
`Hdg^p(H) = ι^{-1}(V^{p,p})`. The preimage of a `ℂ`-subspace under a `ℚ`-linear map is a
`ℚ`-subspace, because `V^{p,p}` is closed under addition and under multiplication by `ℚ ⊂ ℂ`.

**(2)** First, `c(F^p) = ⊕_{a ≥ p} V^{k-a, a}` by the hypothesis `c(V^{a,b}) = V^{b,a}`. Reindex
with `a' = k - a` (so `a' ≤ p`): `c(F^p) = ⊕_{a' ≤ p} V^{a', k-a'}`. Since `V = ⊕ V^{a,b}` is a
direct sum of the components, the intersection of two sums of components is the sum over the
components in both. The components in `F^p` are those with `a ≥ p`, and those in `c(F^p)` are
those with `a ≤ p`. Their common components are those with `a = p`, so

  `F^p ∩ c(F^p) = V^{p,p}`.

Now let `x ∈ H`. Since `c(x ⊗ 1) = x ⊗ \bar 1 = x ⊗ 1`, we have `c(x ⊗ 1) = x ⊗ 1`.

- If `x ∈ Hdg^p(H)`, then `x ⊗ 1 ∈ V^{p,p} ⊆ F^p` and, because `V^{p,p} = F^p ∩ c(F^p)` and
  `c(x⊗1) = x⊗1`, also `c(x ⊗ 1) ∈ F^p`.
- Conversely, if `x ⊗ 1 ∈ F^p` and `c(x ⊗ 1) ∈ F^p`, then `x ⊗ 1 ∈ F^p ∩ c(F^p)`, since
  `x ⊗ 1 = c(x ⊗ 1) ∈ c(F^p)`. This intersection is `V^{p,p}`, so `x ∈ Hdg^p(H)`.

This proves (2). Note that `c(x⊗1) = x⊗1` makes the two conditions in (2) the same condition
on `x ⊗ 1`, once it is known to be in `F^p`. The lemma is correct as stated; its content is
mostly the bookkeeping that the components match.

## Remarks

- The lemma uses only the decomposition and the conjugation property. It does not use a
  polarisation, a Kähler form, or any analysis. So it applies to any weight-`2p` rational Hodge
  structure, not only to those coming from varieties.
- It does not say that `Hdg^p(H)` is spanned by algebraic classes. That is the Hodge conjecture,
  which needs geometry. For an arbitrary rational Hodge structure, `Hdg^p(H)` can contain classes
  not coming from algebraic cycles. The lemma is only about the shape of the set.
- The statement is about Hodge structures, not about varieties. So M1 can be checked in Lean
  without any of the infrastructure listed in the formalization plan.

## Proposed Lean statement (sketch, NOT compiled)

The statement below is a sketch for review. Names are placeholders. It is not a gap file, and it
should not be added to `lean/MPP/` until a maintainer has reviewed the definitions.

```
-- Sketch, not compiled. Intended as the first milestone M1.
structure HodgeStructureWeight (H : Type) [AddCommGroup H] [Module ℚ H] (k : ℕ) where
  decomp : ℕ × ℕ → Submodule ℂ (H ⊗[ℚ] ℂ)   -- V^{a,b}
  -- direct sum over a + b = k, and c-compatibility, to be stated precisely

theorem hodge_classes_submodule (H : Type) [AddCommGroup H] [Module ℚ H]
    [FiniteDimensional ℚ H] (p : ℕ) (hs : HodgeStructureWeight H (2 * p)) :
    ∃ S : Submodule ℚ H, ∀ x : H, x ∈ S ↔ (x ⊗ₜ (1 : ℂ)) ∈ hs.decomp (p, p)
```

## Limits

- The proof above is a paper proof. It has not been checked in Lean or by a second reader.
- The statement is about rational Hodge structures of pure weight `2p` only. Mixed weight is not
  covered.
- The lemma says nothing about the Hodge conjecture or any Millennium Problem.

Licence: CC BY 4.0.
