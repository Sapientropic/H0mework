import H0mework.Fock.HistoryConditional.NativeMergeActual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalMergeLoss

open SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

def decoder (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse)
    (value : Coarse) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (SourceConditionalNativeKeys.word (inventoryBound runtime)
      (SourceConditionalNativeMerge.merge read forget (inventoryBound runtime)
        (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) value).2))

theorem decoder_original (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    decoder runtime read forget = SourceConditionalNativePosterior.decoder runtime (forget ∘ read) := by
  funext value
  rw [decoder, SourceConditionalNativeMerge.merged_generated, SourceConditionalNativePosterior.decoder,
    SourceConditionalNativePosterior.model]
  simp only [map_sum, map_smul]
  change SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (∑ actor : Actors runtime,
      (SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound runtime) value).2 actor •
        SourceConditionalRationalStream.sourceWord (inventoryBound runtime) actor)) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro actor _
  rw [map_smul, ← algebraMap_smul ℂ, map_smul, SourceConditionalRationalStream.source_embed,
    SourceConditionalWordStream.source_read, SourceConditionalInventory.values_original]
  rfl

end
end SourceConditionalMergeLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
