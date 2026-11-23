import Mathlib

/-!
# Birch and Swinnerton-Dyer: definitions

**Draft. This statement needs review by number theorists before any result
stated with it can be taken to mean "BSD is proved" or "BSD is false".**

Mathlib (2026) defines the L-series of a Weierstrass curve over a number field,
`WeierstrassCurve.LSeries`, as the Dirichlet series of its Euler product. For an
elliptic curve `E` over `ℚ` this series converges for `Re s > 3/2`. The rank part
of the conjecture, as posed by the Clay Mathematics Institute, says that the
L-function extends to the whole complex plane and that its order of vanishing
at `s = 1` equals the rank of the group of rational points `E(ℚ)`.

* `BSDRank E`: there is an entire function `F` that agrees with the L-series of
  `E` on `Re s > 3/2` and whose order of vanishing at `1` is the rank of `E(ℚ)`.
  The extension is unique when it exists (identity theorem), so this states the
  conjecture for `E` together with the analytic continuation, which is known
  (modularity theorem) but not yet in Mathlib.
* `BirchSwinnertonDyer`: `BSDRank E` for every elliptic curve `E` over `ℚ`.

The rank is `Module.finrank ℤ E(ℚ)`; by Mordell's theorem (gap `bsd-002`)
`E(ℚ)` is finitely generated, so this is the usual rank.

`E32` is the curve `y² = x³ - x` of conductor 32, used by the first gaps.
-/

namespace MPP.BSD

open WeierstrassCurve

/-- The rank part of the Birch and Swinnerton-Dyer conjecture for `E`. -/
def BSDRank (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = (Module.finrank ℤ E.toAffine.Point : ℕ∞)

/-- The Birch and Swinnerton-Dyer conjecture (rank part) over `ℚ`. -/
def BirchSwinnertonDyer : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], BSDRank E

/-- The elliptic curve `y² = x³ - x` over `ℚ` (conductor 32). -/
def E32 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

end MPP.BSD
