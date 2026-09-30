import H0mework.Physics.LowEnergy.BosonEffective.Taylor
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The actual invertible origin block supplies a nonempty low-momentum domain
and an explicit bound for the untruncated inverse remainder. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
noncomputable section
variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

omit [NormOneClass R] in
theorem perturbation_regular (A G delta : R) (left : G*A=1) (right : A*G=1)
    (small : ‖G*delta‖<1) : IsUnit (A+delta) := by
  have regularA : IsUnit A := ⟨⟨A,G,right,left⟩,rfl⟩
  have regularNext : IsUnit (1+G*delta) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one (x := -(G*delta)) (by simpa using small)
  have factor : A+delta=A*(1+G*delta) := by
    rw [mul_add,mul_one,← mul_assoc,right,one_mul]
  rw [factor]
  exact regularA.mul regularNext

theorem inverse_remainder_bound (A G delta : R) (left : G*A=1) (right : A*G=1)
    (small : ‖G*delta‖<1) :
    ‖Ring.inverse (A+delta)-inverseJet G delta‖≤
      ‖G*delta‖^3*‖Ring.inverse (A+delta)‖ := by
  have regular := perturbation_regular A G delta left right small
  have exactInverse := inverseJet_exact A G delta (Ring.inverse (A+delta)) left (Ring.mul_inverse_cancel _ regular)
  have difference : Ring.inverse (A+delta)-inverseJet G delta= -(G*delta)^3*Ring.inverse (A+delta) := by
    calc
      _ = (inverseJet G delta-G*delta*G*delta*G*delta*Ring.inverse (A+delta))-inverseJet G delta :=
        congrArg (fun x => x-inverseJet G delta) exactInverse
      _ = _ := by noncomm_ring
  rw [difference]
  calc
    _ ≤ ‖-((G*delta)^3)‖*‖Ring.inverse (A+delta)‖ := norm_mul_le _ _
    _ ≤ ‖G*delta‖^3*‖Ring.inverse (A+delta)‖ := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _)

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
