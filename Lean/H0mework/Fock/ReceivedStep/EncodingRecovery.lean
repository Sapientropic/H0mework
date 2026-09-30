import H0mework.Fock.ReceivedStep.EncodingObserver

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem coordinates_injective (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Function.Injective (SourceRationalWindowReadout.coordinates runtime index steps) := by
  intro left right same
  apply Prod.ext
  · funext coordinate
    have bound : cutoff runtime index steps + 1 = (inventoryBound runtime + steps + 1) * (index.val + 1) :=
      (SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime + steps)).trans
        (by rw [SourceCopyProgram.scale_source])
    let original : Fin (cutoff runtime index steps + 1) := ⟨coordinate.val, coordinate.isLt.trans_eq bound.symm⟩
    have actual := congrArg (fun value : SourceCopyCurrentCoordinates.Coordinates runtime index steps => value.1 original) same
    change (left.1 coordinate : ℂ) = (right.1 coordinate : ℂ) at actual
    exact (Rat.cast_injective : Function.Injective (fun scalar : ℚ => (scalar : ℂ))) actual
  · apply Prod.ext
    · exact (Rat.cast_injective : Function.Injective (fun scalar : ℚ => (scalar : ℂ)))
        (congrArg (fun value : SourceCopyCurrentCoordinates.Coordinates runtime index steps => value.2.1) same)
    · exact (Rat.cast_injective : Function.Injective (fun scalar : ℚ => (scalar : ℂ)))
        (congrArg (fun value : SourceCopyCurrentCoordinates.Coordinates runtime index steps => value.2.2) same)

theorem complete_roundtrip (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) :
    SourceRationalWindowReadout.decode (inventoryBound runtime + steps) index.val
      (completeSamples (inventoryBound runtime + steps) index.val data) = data := by
  apply coordinates_injective runtime index steps
  rw [SourceRationalWindowReadout.decode_source runtime index nonunit steps, complete_samples_source,
    SourceOperatorObservationAcquisition.decode_source, completeValue, SourceCopyCurrentCoordinates.realize_source]

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
