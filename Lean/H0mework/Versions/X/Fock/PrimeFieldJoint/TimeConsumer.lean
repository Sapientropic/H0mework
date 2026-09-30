import H0mework.Versions.X.Fock.PrimeFieldJoint.TimeInverse
import H0mework.Probability.MassCompletion.TransferGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointTime

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed SourceGeneratedAcquisitionMeasure
open SourceGeneratedAcquisitionContinuation SourceJointTransfer
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

/-- The fixed seed consumes the complete result without expanding its dependent history type. -/
def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let bound := inventoryBound runtime
    let depth := SourceGeneratedAcquisitionJoint.depth runtime
    (∀ index : Fin (bound + 1), type_of% (next_address bound index) ∧
      type_of% (next_sample_actual depth bound index) ∧ type_of% (window_actor_factorizes bound (Fin.cast (congrArg (· + 1) (runtime_bound bound).symm) index))) ∧
    (∀ value : FieldSpace depth bound, type_of% (next_word_transfer depth bound value) ∧
      type_of% (next_joint_transfer depth bound value) ∧ type_of% (next_joint_norm depth bound value) ∧
      type_of% (next_joint_mass depth bound value)) ∧
    (∀ value : NextSpace depth bound, type_of% (original_pullback_is_whole_transfer depth bound value) ∧
      type_of% (next_residual_zero depth bound value)) ∧
    (∀ value : SourceMassCompletion.Joint, type_of% (whole_transfer value) ∧
      type_of% (whole_residual_source value) ∧ type_of% (whole_energy value) ∧ type_of% (action_range value)) ∧
    (∀ left right : SourceMassCompletion.Joint,
      type_of% (IsometricRetainedTransfer.transfer_fibre_iff SourceMassCompletion.action left right)) ∧
    wholeTransfer (SourceMassCompletion.nativeRead (sourcePoint runtimeSeed.state)) =
      WithLp.toLp 2 ((0 : SourceShift.H), (1 : ℂ)) ∧
    type_of% root_unit_residual ∧ type_of% root_unit_not_in_range ∧
    type_of% SourceMassCompletion.generated_limit_mass ∧ type_of% SourceMassCompletion.generated_limit_ne_zero ∧
    type_of% (SourceGeneratedAcquisitionJoint.sourceGeneratedAcquisitionJointRecovery round) ∧
    type_of% (runtime_eq runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave)

theorem sourceGeneratedJointTimeRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨(fun index => ⟨next_address _ index, next_sample_actual _ _ index, window_actor_factorizes _ (Fin.cast (congrArg (· + 1) (runtime_bound _).symm) index)⟩),
    (fun value => ⟨next_word_transfer _ _ value, next_joint_transfer _ _ value,
      next_joint_norm _ _ value, next_joint_mass _ _ value⟩),
    (fun value => ⟨original_pullback_is_whole_transfer _ _ value, next_residual_zero _ _ value⟩),
    (fun value => ⟨whole_transfer value, whole_residual_source value, whole_energy value, action_range value⟩),
    (fun left right => IsometricRetainedTransfer.transfer_fibre_iff SourceMassCompletion.action left right),
    root_unit_transfer, root_unit_residual, root_unit_not_in_range,
    SourceMassCompletion.generated_limit_mass, SourceMassCompletion.generated_limit_ne_zero,
    SourceGeneratedAcquisitionJoint.sourceGeneratedAcquisitionJointRecovery round,
    runtime_eq _, coversAt_factorizes _ .particleWave, coversAt_factorizes _ .particleWave⟩

end
end SourceGeneratedJointTime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
