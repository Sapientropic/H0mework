import H0mework.Fock.InverseOptimal.Positive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimal

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ word : List (Fock.Letter (inventoryBound runtime)),
    (∀ value candidate : SourceJointClockGraph.Carrier,
      type_of% (error_decomposition (inventoryBound runtime) word value candidate) ∧
      type_of% (optimal (inventoryBound runtime) word value candidate) ∧
      type_of% (optimal_unique (inventoryBound runtime) word value candidate)) ∧
    ∀ key : ZMod 2,
      type_of% (SourceInverseDistributionLoss.model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
      ∀ candidate : SourceJointClockGraph.Carrier,
        type_of% (conditional_cost runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported candidate) ∧
        type_of% (field_cost runtime (inventoryBound runtime) word key supported candidate) ∧
        type_of% (field_optimal runtime (inventoryBound runtime) word key supported candidate) ∧
        type_of% (field_unique runtime (inventoryBound runtime) word key supported candidate)) ∧
  ∀ candidate : SourceJointClockGraph.Carrier,
    type_of% (no_double_shift_recovery runtime (inventoryBound runtime) (fun index : Nat => (index : ZMod 2)) candidate)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes,
    (fun word => ⟨(fun value candidate => ⟨error_decomposition (inventoryBound runtime) word value candidate,
      optimal (inventoryBound runtime) word value candidate, optimal_unique (inventoryBound runtime) word value candidate⟩),
      fun key => ⟨SourceInverseDistributionLoss.model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
        fun supported candidate => ⟨conditional_cost runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported candidate,
          field_cost runtime (inventoryBound runtime) word key supported candidate, field_optimal runtime (inventoryBound runtime) word key supported candidate,
          field_unique runtime (inventoryBound runtime) word key supported candidate⟩⟩⟩),
    fun candidate => no_double_shift_recovery runtime (inventoryBound runtime) (fun index : Nat => (index : ZMod 2)) candidate⟩

end
end SourceInverseDistributionOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
