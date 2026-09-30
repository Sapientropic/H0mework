import H0mework.Probability.Empirical.Error
import H0mework.Probability.EmpiricalRecovery.Model
import H0mework.Fock.SourceHistory.ConditionalTransferReadoutRegression

/-! The original pulse gives a sharp recovery floor for every decoder of its actual next observation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.Pulse

open SourceGeneratedEmpiricalHilbert SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer SourceConditionalTransfer.Pulse
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceOperationNative.Observed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem residual_energy : ‖residual pulse runtime 1 indicatorValue‖ ^ 2 = (1 / 4 : ℝ) := by
  rw [sample_norm_sq, Fin.sum_univ_two, residual_zero_value, residual_one_value]
  norm_num [historyPMF_apply]

theorem any_decoder_error (decoder : Field pulse → ℂ) :
    (1 / 4 : ℝ) ≤ sourceError pulse runtime 1 indicatorValue decoder :=
  residual_energy ▸ residual_lower_bound pulse runtime 1 indicatorValue decoder

theorem transfer_attains_quarter :
    sourceError pulse runtime 1 indicatorValue (fun atom => transfer pulse runtime 1 indicatorValue atom) =
      (1 / 4 : ℝ) :=
  (transfer_attains pulse runtime 1 indicatorValue).trans residual_energy

theorem no_exact_decoder (decoder : Field pulse → ℂ) :
    ¬ ∀ index : Fin 2,
      decoder (nextAtom pulse runtime 1 index) = indicatorValue (fieldSample pulse runtime 1 index) := by
  intro recovers
  have zeroError : sourceError pulse runtime 1 indicatorValue decoder = 0 := by
    simp [sourceError, recovers]
  have lower := any_decoder_error decoder
  rw [zeroError] at lower
  norm_num at lower

theorem current_models_distinct :
    modelPoint (process := process) pulse (runtimeAt 0) ≠ modelPoint (process := process) pulse (runtimeAt 1) := by
  intro same
  have observations := (model_native_fibre_iff (process := process) pulse (runtimeAt 0) (runtimeAt 1)).mp same
  have points := (native_fibre_iff (process := process) pulse (runtimeAt 0) (runtimeAt 1)).mpr observations
  exact point_zero_ne_one points

theorem next_models_equal :
    modelPoint (process := process) pulse ((history runtime 1).stageAt 0).next =
      modelPoint (process := process) pulse ((history runtime 1).stageAt 1).next :=
  (nextAtom_model_iff pulse runtime 1 0 1).mp
    ((nextObservation_constant 0).trans (nextObservation_constant 1).symm)

end
end SourceConditionalRecovery.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
