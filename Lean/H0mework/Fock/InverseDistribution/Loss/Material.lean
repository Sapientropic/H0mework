import H0mework.Fock.InverseDistribution.Positive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionLoss

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ word : List (Fock.Letter (inventoryBound runtime)),
    (∀ weights : Fin (inventoryBound runtime + 1) → ℚ, type_of% (residual_norm (inventoryBound runtime) (inventoryBound runtime) word weights)) ∧
    ∀ key : ZMod 2,
      type_of% (generated_residual_norm runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
        type_of% (conditional_cost runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported) ∧
        type_of% (field_cost runtime (inventoryBound runtime) word key supported)) ∧
  type_of% (double_shift_loss_positive (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime)) ∧
  type_of% (double_shift_not_restored runtime (inventoryBound runtime) (fun index : Nat => (index : ZMod 2)))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes,
    (fun word => ⟨(fun weights => residual_norm (inventoryBound runtime) (inventoryBound runtime) word weights),
      fun key => ⟨generated_residual_norm runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key, model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
        fun supported => ⟨conditional_cost runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported,
          field_cost runtime (inventoryBound runtime) word key supported⟩⟩⟩),
    double_shift_loss_positive (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime),
    double_shift_not_restored runtime (inventoryBound runtime) (fun index : Nat => (index : ZMod 2))⟩

end
end SourceInverseDistributionLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
