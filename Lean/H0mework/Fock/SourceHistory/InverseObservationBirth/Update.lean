import H0mework.Fock.SourceHistory.InverseObservationBirth.Packet
import H0mework.Fock.HistoryConditional.NativeBirthUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem decoder_update {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyTimeModel.restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
      (packet runtime depth word read key) =
    if key = read (inventoryBound runtime + 1) then
      SourceConditionalNativePosterior.decoder runtime read key +
        ((((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) •
          (SourceConditionalInventory.born (inventoryBound runtime) - SourceConditionalNativePosterior.decoder runtime read key)
    else SourceConditionalNativePosterior.decoder runtime read key := by
  dsimp only
  rw [recovered, SourceConditionalNativeBirth.decoder_next]

theorem model_update {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
      (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next.tick.next)
      (SourceCopyTimeModel.restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
        (packet runtime depth word read key)) = SourceConditionalNativeBirth.update runtime read key := by
  dsimp only
  rw [recovered, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization,
    SourceConditionalNativeBirth.update_is_next]

end
end SourceInverseObservationBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
