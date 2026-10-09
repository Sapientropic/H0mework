import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldResolvent

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open ActualDressedNumberSector ActualDressedNumberZero ActualDressedSourcePreparation
open Filter
open scoped Topology
local instance fieldTimeReal : NormedAlgebra ℝ ActualDressedNumberZero.Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance fieldTimeRational : NormedAlgebra ℚ ActualDressedNumberZero.Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] numberTwoProjection physicalTime

private theorem exp_range {B : Type*} [NormedRing B] [NormedAlgebra ℚ B] [CompleteSpace B]
    (P X : B) (idem : P*P=P) (range : P*X*P=X*P) : P*NormedSpace.exp X*P=NormedSpace.exp X*P := by
  have source : SemiconjBy P (P*X*P) X := by
    change P*(P*X*P)=X*P
    calc
      _=(P*P)*X*P := by noncomm_ring
      _=P*X*P := by rw [idem]
      _=X*P := range
  have generated:=source.exp_right.eq
  calc
    _=P*(NormedSpace.exp X*P) := by rw [mul_assoc]
    _=P*(P*NormedSpace.exp (P*X*P)) := by rw [←generated]
    _=(P*P)*NormedSpace.exp (P*X*P) := (mul_assoc P P _).symm
    _=P*NormedSpace.exp (P*X*P) := by rw [idem]
    _=NormedSpace.exp X*P := generated

private theorem scalar_range {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℝ B]
    (P X : B) (c : ℂ) (t : ℝ) (range : P*X*P=X*P) : P*(t • (c • X))*P=(t • (c • X))*P := by
  simp only [mul_smul_comm,smul_mul_assoc]
  exact congrArg (fun Y : B=>t • (c • Y)) range

/-- The unchanged physicalTime(h) preserves the actual N2 carrier throughout the original field family. -/
theorem actual_joint_time_number_two_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (h : Field289) : numberTwoProjection*physicalTime p F t h*numberTwoProjection=
      physicalTime p F t h*numberTwoProjection := by
  unfold physicalTime SourceFiniteUnitary.time
  apply exp_range _ _ actual_number_two_square
  exact scalar_range (B:=ActualDressedNumberZero.Op) _ _ (-Complex.I) t
    (actual_joint_generator_number_two p F 0 h)

theorem actual_joint_time_created_number_two (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t epsilon : ℝ) (precision : 0<epsilon) (h : Field289) :
    numberTwoProjection (physicalTime p F t h (sourceDressedUnit epsilon precision))=
      physicalTime p F t h (sourceDressedUnit epsilon precision) := by
  have source:=congrArg (fun A : ActualDressedNumberZero.Op=>A (sourceDressedUnit epsilon precision))
    (actual_joint_time_number_two_range p F t h)
  simpa only [mul_apply_eq_comp,actual_created_unit_N2] using source

/-- The actual fixed prepared unit and every original time directly consume the generated right Green field germ. -/
theorem actual_joint_created_inverse_time_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (epsilon : ℝ) (precision : 0<epsilon) :
    ∀ᶠh : Field289 in 𝓝 0,∀t : ℝ,
    jointResolvent p F z h (physicalTime p F t h (sourceDressedUnit epsilon precision))=
      jointN2GreenWords p F z h (physicalTime p F t h (sourceDressedUnit epsilon precision)) := by
  filter_upwards [actual_joint_N2_resolvent_return p F z nonreal] with h source
  intro t
  have returned:=congrArg (fun A : ActualDressedNumberZero.Op=>
    A (physicalTime p F t h (sourceDressedUnit epsilon precision))) source
  simpa only [mul_apply_eq_comp,actual_joint_time_created_number_two] using returned

end LowEnergy.GaussComposite.ActualDressedNumberField
