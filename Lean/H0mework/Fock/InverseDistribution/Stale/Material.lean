import H0mework.Fock.InverseDistribution.Stale.Feedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionStale

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    type_of% (stale_loss runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (penalty_positive runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (stale_strict runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))) ∧
    type_of% (field_stale_strict runtime (inventoryBound runtime) word) ∧
    ∀ key : ZMod 2,
      type_of% (decoder_clock_le runtime (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (SourceInverseDistributionLoss.model_feedback runtime.tick.next (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨stale_loss runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)),
    penalty_positive runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)), stale_strict runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)),
    field_stale_strict runtime (inventoryBound runtime) word,
    fun key => ⟨decoder_clock_le runtime (fun index : Nat => (index : ZMod 2)) key,
      SourceInverseDistributionLoss.model_feedback runtime.tick.next (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key⟩⟩⟩

end
end SourceInverseDistributionStale
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
