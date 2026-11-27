import Mathlib
import MPP.Solutions.Bsd244
import MPP.Solutions.Bsd245

namespace MPP.Solutions.Bsd351

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    p ≠ 2 → ¬ (p : ℤ) ∣ 3 →
    (Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // (3 : ℤ) • P = 0} : ℤ) = (3 : ℤ) ^ 2 := by
  intro p _ _ W _ hp2 hp3
  have h2 : (2 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : AlgebraicClosure (ZMod p)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have h3 : (3 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure (ZMod p)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at h'
    apply hp3
    exact_mod_cast h'
  haveI : (W.baseChange (AlgebraicClosure (ZMod p))).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsElliptic)
  have hup := MPP.Solutions.Bsd245.main (AlgebraicClosure (ZMod p)) (W.baseChange (AlgebraicClosure (ZMod p))) h3
  have hlo := MPP.Solutions.Bsd244.main (AlgebraicClosure (ZMod p)) (W.baseChange (AlgebraicClosure (ZMod p))) h2 h3
  have hcard := le_antisymm hup hlo
  exact (congrArg (fun n : ℕ => (n : ℤ)) hcard).trans (by norm_num)

end MPP.Solutions.Bsd351
