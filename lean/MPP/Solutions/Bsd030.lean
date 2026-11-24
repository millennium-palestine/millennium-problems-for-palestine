import Mathlib

namespace MPP.Solutions.Bsd030

-- the rationals whose numerator and denominator are bounded by M form a finite set
theorem finite_bounded_rat (M : ℕ) : {x : ℚ | x.num.natAbs ≤ M ∧ x.den ≤ M}.Finite := by
  refine (((Set.finite_Icc (-(M : ℤ)) M).prod (Set.finite_Icc 1 M)).image
    (fun q : ℤ × ℕ => (q.1 : ℚ) / (q.2 : ℚ))).subset ?_
  rintro x ⟨hn, hd⟩
  have hn' : (x.num.natAbs : ℤ) ≤ M := by exact_mod_cast hn
  have hb := abs_le.mp (by rwa [Int.natCast_natAbs] at hn' : |x.num| ≤ M)
  refine ⟨(x.num, x.den), ⟨⟨hb.1, hb.2⟩, ⟨x.den_pos, hd⟩⟩, Rat.num_div_den x⟩

-- for fixed x, the equation y² + b y = c has finitely many solutions y
theorem finite_quadratic_roots (b c : ℚ) : {y : ℚ | y ^ 2 + b * y = c}.Finite := by
  have hP : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X - Polynomial.C c : Polynomial ℚ) ≠ 0 := by
    intro h
    have h2 := congrArg (fun q : Polynomial ℚ => q.coeff 2) h
    simp at h2
  refine (Polynomial.finite_setOf_isRoot hP).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination hy

theorem main : ∀ (a₁ a₂ a₃ a₄ a₆ : ℚ) (M : ℕ),
    {p : ℚ × ℚ | p.2 ^ 2 + a₁ * p.1 * p.2 + a₃ * p.2 = p.1 ^ 3 + a₂ * p.1 ^ 2 + a₄ * p.1 + a₆ ∧
      p.1.num.natAbs ≤ M ∧ p.1.den ≤ M}.Finite := by
  intro a₁ a₂ a₃ a₄ a₆ M
  refine ((finite_bounded_rat M).biUnion fun x _ =>
    ((finite_quadratic_roots (a₁ * x + a₃) (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)).image
      fun y => (x, y))).subset ?_
  rintro ⟨x, y⟩ ⟨hcurve, hnum, hden⟩
  dsimp only at hcurve hnum hden
  refine Set.mem_biUnion (x := x) ⟨hnum, hden⟩ ⟨y, ?_, rfl⟩
  show y ^ 2 + (a₁ * x + a₃) * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆
  linear_combination hcurve

end MPP.Solutions.Bsd030
