import H0mework.Versions.X.Fock.SourceHistory.PrimeClockSplittingRegression

/-! Source-generated full coordinates and actual next action are consumed by the original information and ledger chain. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalTransfer SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem whole_chart_consumed (bound width : Nat) :
    let current := SourcePrimeObservationDelay.startRuntime sourceOwner bound width
    let stage := (history current bound).stageAt (Fin.last bound)
    (∀ value : SourcePrimeCompletion.Field, ∀ clock : ℤ, type_of% (full_inverse_fibre value clock)) ∧
      (∀ value : JointField, type_of% (rebuild_coordinates value) ∧ type_of% (action_equation value)) ∧
      (∀ source : SourceOperationNative.Carrier process,
        type_of% (source_reconstruction source) ∧ type_of% (source_section_fibre source)) ∧
      type_of% joint_action_injective ∧ type_of% no_preimage_native_unit ∧
      type_of% unit_section_not_source ∧ type_of% section_not_equivariant ∧ type_of% native_unit_keeps_clock ∧
      (∀ actor : Fin (bound + 1), type_of% (actual_query_from_chart current bound actor) ∧
        type_of% (chart_restores_model current bound actor) ∧ type_of% (original_transfer_from_chart current bound actor) ∧
        type_of% (native_action_equation (current.advance actor.val)) ∧ type_of% (query_material current bound actor)) ∧
      coordinates (fieldPoint (process := process) jointRead stage.next.state) =
        (fieldAction (process := process) rawField (fieldPoint (process := process) rawField (current.advance bound).state),
          SourceClockModel.rawClock (current.advance bound).state + 1) ∧
      type_of% (SourcePrimeClockResidual.joint_information_consumed bound width) := by
  exact ⟨full_inverse_fibre, (fun value => ⟨rebuild_coordinates value, action_equation value⟩),
    (fun source => ⟨source_reconstruction source, source_section_fibre source⟩),
    joint_action_injective, no_preimage_native_unit, unit_section_not_source, section_not_equivariant, native_unit_keeps_clock,
    (fun actor => ⟨actual_query_from_chart _ bound actor, chart_restores_model _ bound actor,
      original_transfer_from_chart _ bound actor, native_action_equation _, query_material _ bound actor⟩),
    native_action_equation _, SourcePrimeClockResidual.joint_information_consumed bound width⟩

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
