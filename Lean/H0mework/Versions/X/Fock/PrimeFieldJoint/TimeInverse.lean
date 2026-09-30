import H0mework.Versions.X.Fock.PrimeFieldJoint.TimeSource
import H0mework.Probability.MassCompletion.Transfer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointTime

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceJointTransfer
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev timePullback (depth bound : Nat) : NextSpace depth bound →ₗᵢ[ℂ] FieldSpace depth bound :=
  SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound

theorem next_joint_pullback (depth bound : Nat) (value : NextSpace depth bound) :
    nextJoint depth bound value = SourceMassCompletion.action
      (SourceGeneratedAcquisitionJoint.joint depth bound (timePullback depth bound value)) := by
  have actual := next_joint_transfer depth bound (timePullback depth bound value)
  rw [show timeTransfer depth bound (timePullback depth bound value) = value from
    IsometricRetainedTransfer.transfer_pullback (timePullback depth bound) value] at actual
  exact actual

theorem original_pullback_is_whole_transfer (depth bound : Nat) (value : NextSpace depth bound) :
    SourceGeneratedAcquisitionJoint.joint depth bound (timePullback depth bound value) =
      wholeTransfer (nextJoint depth bound value) := by
  rw [next_joint_pullback]
  exact (IsometricRetainedTransfer.transfer_pullback SourceMassCompletion.action _).symm

theorem next_residual_zero (depth bound : Nat) (value : NextSpace depth bound) :
    wholeResidual (nextJoint depth bound value) = 0 := by
  rw [next_joint_pullback]
  change SourceMassCompletion.action _ - SourceMassCompletion.action
    (IsometricRetainedTransfer.transfer SourceMassCompletion.action (SourceMassCompletion.action _)) = 0
  rw [IsometricRetainedTransfer.transfer_pullback, sub_self]

theorem next_joint_norm (depth bound : Nat) (value : FieldSpace depth bound) :
    ‖nextJoint depth bound (timeTransfer depth bound value)‖ = ‖SourceGeneratedAcquisitionJoint.joint depth bound value‖ := by
  rw [next_joint_transfer, SourceMassCompletion.action.norm_map]

theorem next_joint_mass (depth bound : Nat) (value : FieldSpace depth bound) :
    SourceMassCompletion.massRead (nextJoint depth bound (timeTransfer depth bound value)) =
      SourceMassCompletion.massRead (SourceGeneratedAcquisitionJoint.joint depth bound value) := by
  rw [next_joint_transfer, SourceMassCompletion.massRead_action]

end
end SourceGeneratedJointTime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
