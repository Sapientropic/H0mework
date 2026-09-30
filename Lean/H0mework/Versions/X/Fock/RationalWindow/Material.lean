import H0mework.Versions.X.Fock.RationalWindow.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0),
    (∀ (steps : Nat) (samples : Samples (inventoryBound runtime + steps) (index.val + 1)),
      type_of% (decode_source runtime index nonunit steps samples) ∧
      type_of% (decoded_readout runtime index nonunit steps samples)) ∧
    ∀ key : ZMod 2,
      type_of% (recovered_posterior runtime index nonunit (fun n : Nat => (n : ZMod 2)) key) ∧
      type_of% (decoded_reconstruction runtime index nonunit (fun n : Nat => (n : ZMod 2)) key)) ∧
  (∀ (nonunit : (maximumIndex runtime).val ≠ 0)
      (samples : Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)),
    type_of% (decoded_model runtime nonunit samples)) ∧
  ∀ key : ZMod 2, type_of% (next_recovered runtime (fun n : Nat => (n : ZMod 2)) key)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes,
    fun index nonunit => ⟨fun steps samples => ⟨decode_source runtime index nonunit steps samples,
      decoded_readout runtime index nonunit steps samples⟩,
      fun key => ⟨recovered_posterior runtime index nonunit (fun n : Nat => (n : ZMod 2)) key,
        decoded_reconstruction runtime index nonunit (fun n : Nat => (n : ZMod 2)) key⟩⟩,
    fun nonunit samples => decoded_model runtime nonunit samples,
    fun key => next_recovered runtime (fun n : Nat => (n : ZMod 2)) key⟩

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
