import H0mework.Fock.InverseDistribution.InverseDistribution.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeInverseDistribution

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    (∀ weights : Fin (inventoryBound runtime + 1) → ℚ,
      type_of% (reconstruction (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (SourceCompiledWordOperator.slope_positive _) weights) ∧
      type_of% (g_reconstruction (inventoryBound runtime) (inventoryBound runtime) word weights) ∧
      type_of% (residual_recovery (inventoryBound runtime) (inventoryBound runtime) word weights)) ∧
    ∀ key : ZMod 2,
      type_of% (decoder_reconstruction runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (decoder_moments runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (decoder_residual runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨(fun weights =>
    ⟨reconstruction (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _) weights,
      g_reconstruction (inventoryBound runtime) (inventoryBound runtime) word weights,
      residual_recovery (inventoryBound runtime) (inventoryBound runtime) word weights⟩),
    fun key => ⟨decoder_reconstruction runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      decoder_moments runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      decoder_residual runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key⟩⟩⟩

end
end SourceNativeInverseDistribution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
