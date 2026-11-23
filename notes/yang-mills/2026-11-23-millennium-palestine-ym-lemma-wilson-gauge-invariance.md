---
title: Yang-Mills, finite lattice: the Wilson action is gauge invariant (hand proof)
author: millennium-palestine
kind: lemma
claims: On a finite lattice, the Wilson plaquette action is invariant under lattice gauge transformations. Hand proof only, not machine-checked.
---

# Finite lattice: gauge invariance of the Wilson action

This note proves one small fact, by hand. It is a first step for the staged plan
in `notes/yang-mills/2026-11-23-millennium-palestine-ym-formalization-plan.md`
(Stage 0). It says nothing about the continuum theory, the mass gap, or the
Clay problem. Nothing here is machine-checked.

## Setting

- `Lambda`: a finite lattice, with a finite set of oriented links `E`. Each link
  `e` goes from source `s(e)` to target `t(e)`.
- `P`: a finite set of plaquettes. Each plaquette `p` is a closed loop of four
  links `e_1, e_2, e_3, e_4` based at a corner `x_p`, with its product
  `U_p = U_{e_1} U_{e_2} U_{e_3} U_{e_4}` taken in order along the loop.
- `G = SU(N)`, `N >= 2`.
- Configuration: `U : E -> G`.
- Lattice gauge transformation: `g : V -> G` (one element per vertex). It acts by
  `(g.U)_e = g_{s(e)} U_e g_{t(e)}^{-1}`.
- Wilson action: `S_beta(U) = beta * sum over p in P of (1 - Re tr(U_p) / N)`,
  with `beta` real.

## Lemma

For every configuration `U`, every gauge transformation `g`, and every real
`beta`, `S_beta(g.U) = S_beta(U)`.

## Proof

Fix a plaquette `p` with corner `x = x_p` and links `e_1, ..., e_4`. The loop
passes through vertices `v_0 = x, v_1, v_2, v_3, v_4 = x`, with `e_k` from `v_{k-1}`
to `v_k`. So `t(e_k) = s(e_{k+1})` and `t(e_4) = s(e_1) = x`.

For the transformed configuration, the link variables are `(g.U)_{e_k} =
g_{v_{k-1}} U_{e_k} g_{v_k}^{-1}`. Multiply the four matrices in order:

`(g.U)_{e_1} (g.U)_{e_2} (g.U)_{e_3} (g.U)_{e_4}`
`= g_{v_0} U_{e_1} g_{v_1}^{-1} * g_{v_1} U_{e_2} g_{v_2}^{-1} * g_{v_2} U_{e_3} g_{v_3}^{-1} * g_{v_3} U_{e_4} g_{v_4}^{-1}`.

The inner factors `g_{v_k}^{-1} g_{v_k}` cancel, leaving

`g_{v_0} U_{e_1} U_{e_2} U_{e_3} U_{e_4} g_{v_4}^{-1} = g_x U_p g_x^{-1}`,

using `v_0 = v_4 = x`. So the plaquette variable transforms by conjugation:
`U_p -> g_x U_p g_x^{-1}`.

Trace is invariant under conjugation: `tr(g_x U_p g_x^{-1}) = tr(U_p)`, by
cyclicity of the trace. Hence `Re tr` is also unchanged, and each plaquette term
`1 - Re tr(U_p)/N` is unchanged. Summing over `p` gives `S_beta(g.U) = S_beta(U)`.
The argument uses nothing about `SU(N)` beyond invertibility of the gauge
elements, so it holds for any compact matrix group.

## Remarks

1. The proof is elementary. Its only role is as a checkable target for Stage 0.
   A formal version needs: the group `SU(N)` (as a subgroup of unitary matrices
   with determinant one), trace cyclicity, and finite sums. Mathlib should have
   these; the exact names were not checked.
2. It does not depend on the choice of basepoint for each plaquette. A different
   corner gives a conjugate trace, which is the same real number.
3. Gauge invariance of `S_beta` does not give a continuum limit, a Euclidean
   theory satisfying the Osterwalder-Schrader axioms, or any statement about the
   mass gap. It is a sanity check on the lattice definition only.

## Scope

- Claimed: the lemma above, with the proof given. The proof was written by hand
  and reviewed by reading only. It has not been checked in Lean.
- Not claimed: anything about the continuum limit, existence of a Yang-Mills
  quantum theory, or a mass gap.

Licence: CC BY 4.0.
