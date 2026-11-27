import Mathlib
import MPP.Solutions.Bsd231
import MPP.Solutions.Bsd234

namespace MPP.Solutions.Bsd350

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    ¬ (p : ℤ) ∣ 2 →
    (Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // (2 : ℤ) • P = 0} : ℤ) = (2 : ℤ) ^ 2 := by
  intro p _ _ W _ hp
  have h2 : (2 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h
    apply hp
    have h' : ((2 : ℕ) : AlgebraicClosure (ZMod p)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at h'
    exact_mod_cast h'
  haveI : (W.baseChange (AlgebraicClosure (ZMod p))).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsElliptic)
  have hup := MPP.Solutions.Bsd231.main (AlgebraicClosure (ZMod p)) (W.baseChange (AlgebraicClosure (ZMod p))) h2
  have hlo := MPP.Solutions.Bsd234.main (AlgebraicClosure (ZMod p)) (W.baseChange (AlgebraicClosure (ZMod p))) h2
  have hcard := le_antisymm hup hlo
  have hiff : ∀ P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point,
      (2 : ℤ) • P = 0 ↔ (2 : ℕ) • P = 0 := by
    intro P
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, natCast_zsmul]
  have heq := Nat.card_congr (Equiv.subtypeEquivRight hiff)
  exact (heq ▸ congrArg (fun n : ℕ => (n : ℤ)) hcard).trans (by norm_num)

end MPP.Solutions.Bsd350
