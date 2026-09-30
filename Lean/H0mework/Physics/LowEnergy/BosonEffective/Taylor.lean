import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.NoncommRing

/-! The invertible source-origin block generates an exact second-order
inverse with a cubic remainder. Zero matter directions need not be inverted. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
noncomputable section
variable {R : Type*} [Ring R]

def inverseJet (G delta : R) : R := G-G*delta*G+G*delta*G*delta*G

theorem inverseJet_residual (A G delta : R) (right : A*G=1) :
    (A+delta)*inverseJet G delta=1+delta*G*delta*G*delta*G := by
  unfold inverseJet
  calc
    _ = A*G-(A*G)*delta*G+(A*G)*delta*G*delta*G+
      delta*G-delta*G*delta*G+delta*G*delta*G*delta*G := by noncomm_ring
    _ = _ := by rw [right]; noncomm_ring

theorem inverseJet_exact (A G delta actualInverse : R)
    (left : G*A=1) (right : (A+delta)*actualInverse=1) :
    actualInverse=inverseJet G delta-G*delta*G*delta*G*delta*actualInverse := by
  have step : G=actualInverse+G*delta*actualInverse := by
    calc
      _ = G*((A+delta)*actualInverse) := by rw [right,mul_one]
      _ = (G*A)*actualInverse+G*delta*actualInverse := by noncomm_ring
      _ = _ := by rw [left,one_mul]
  unfold inverseJet
  have solve : actualInverse=G-G*delta*actualInverse := eq_sub_of_add_eq step.symm
  calc
    actualInverse = G-G*delta*actualInverse := solve
    _ = G-G*delta*(G-G*delta*actualInverse) := congrArg (fun x => G-G*delta*x) solve
    _ = G-G*delta*G+G*delta*G*delta*actualInverse := by noncomm_ring
    _ = G-G*delta*G+G*delta*G*delta*(G-G*delta*actualInverse) :=
      congrArg (fun x => G-G*delta*G+G*delta*G*delta*x) solve
    _ = _ := by noncomm_ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
