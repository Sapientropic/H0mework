import H0mework.Fock.InverseBirth.Field
import H0mework.Fock.HistoryConditional.NativeBirthInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimalBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  type_of% (SourceConditionalNativeBirth.information_next runtime (fun index : Nat => (index : ZMod 2))) ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    (∀ key : ZMod 2,
      type_of% (inverse_next runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (decoder_next runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (SourceInverseDistributionLoss.model_feedback runtime.tick.next (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key)) ∧
    (∀ guess : ZMod 2 → SourceJointClockGraph.Carrier,
      type_of% (total_decomposition runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) guess) ∧
      type_of% (total_optimal runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) guess)) ∧
    type_of% (minimum_update runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (source_increment runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (field_total runtime (inventoryBound runtime) word) ∧
    type_of% (field_minimum_update runtime (inventoryBound runtime) word) ∧
    type_of% (minimum_monotone runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (born_cost (inventoryBound runtime) (inventoryBound runtime) word)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, SourceConditionalNativeBirth.information_next runtime (fun index : Nat => (index : ZMod 2)),
    fun word => ⟨(fun key => ⟨inverse_next runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key, decoder_next runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      SourceInverseDistributionLoss.model_feedback runtime.tick.next (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key⟩),
      (fun guess => ⟨total_decomposition runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) guess, total_optimal runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) guess⟩),
      minimum_update runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)), source_increment runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)), field_total runtime (inventoryBound runtime) word,
      field_minimum_update runtime (inventoryBound runtime) word, minimum_monotone runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)), born_cost (inventoryBound runtime) (inventoryBound runtime) word⟩⟩

end
end SourceInverseDistributionOptimalBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
