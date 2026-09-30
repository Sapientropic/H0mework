import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertConsumer
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.Residual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedActionWords.Fock
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance codeConsumerWordsMeasurable (depth : Nat) : MeasurableSpace (Complete.Carrier depth) :=
  Dynamic.Hilbert.measurable depth
local instance codeConsumerFieldMeasurable (depth : Nat) :
    MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem original_code_time_consumed (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Letter (inventoryBound runtime + 1)))
    (task : SourceConditionalModel.Actors runtime → ℂ)
    (key : ZMod 2)
    (supported : key ∈ (SourceConditionalHistory.observed
      (SourceConditionalHistory.observed (historyPMF (inventoryBound runtime))
        (Actor.nextRead (inventoryBound runtime + 1) (inventoryBound runtime)))
      (fieldCode (inventoryBound runtime) word)).support)
    (value : SourceWeightedRecovery.Space
      (wordLaw (inventoryBound runtime + 1) CanonicalUnitArithmeticRoot.initialCurrent
        (inventoryBound runtime))) :
    type_of% (counted_original_field_transfer runtime nonunit word task key supported) ∧
      type_of% (field_to_code_residual (inventoryBound runtime) word task) ∧
      type_of% (sourceTime_original_residual (inventoryBound runtime + 1)
        CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime) value) ∧
      type_of% (sourceTime_original_reconstruction (inventoryBound runtime + 1)
        CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime) value) ∧
      type_of% (original_time_information_consumed (inventoryBound runtime) task) ∧
      type_of% ((SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes) :=
  ⟨counted_original_field_transfer runtime nonunit word task key supported,
    field_to_code_residual (inventoryBound runtime) word task,
    sourceTime_original_residual (inventoryBound runtime + 1)
      CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime) value,
    sourceTime_original_reconstruction (inventoryBound runtime + 1)
      CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime) value,
    original_time_information_consumed (inventoryBound runtime) task,
    (SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes⟩

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
