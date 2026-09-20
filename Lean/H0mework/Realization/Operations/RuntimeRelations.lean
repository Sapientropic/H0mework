import H0mework.Realization.Operations.RuntimeSuccessor
import H0mework.Realization.Operations.ScalarExact

/-! The complete runtime fibres consume the already generated scalar relation kernel. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime

open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation

noncomputable section

universe r u m n

variable {N : WorldRelationNetwork.{n}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

def stageRelationMap {runtime : LivingRuntimeState process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :=
  relationMap (R := R) (s := s)
    (pairEnvironment (oldEnvironment readMaterial environment stage)
      (incrementEnvironment readMaterial environment stage))

theorem stage_fibre_generated {runtime : LivingRuntimeState process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) (left right : FormalCarrier R Value Var s) :
    stageInventory readMaterial environment stage left = stageInventory readMaterial environment stage right ↔
      liftMap (R := R) (left - right) ∈ LinearMap.range
        (stageRelationMap (R := R) (s := s) readMaterial environment stage) :=
  inventory_fibre_generated (oldEnvironment readMaterial environment stage)
    (incrementEnvironment readMaterial environment stage) left right

theorem completion_fibre_generated (runtime : LivingRuntimeState process)
    (left right : FormalCarrier R Value Var s) :
    (completionMap readMaterial environment runtime).hom left =
        (completionMap readMaterial environment runtime).hom right ↔
      ∀ bound (index : Fin (bound + 1)),
        liftMap (R := R) (left - right) ∈ LinearMap.range
          (stageRelationMap (R := R) (s := s) readMaterial environment
            ((materialHistory runtime bound).stageAt index)) := by
  rw [completion_fibre_iff]
  constructor
  · intro readings bound index
    exact (stage_fibre_generated readMaterial environment _ left right).mp (readings bound index)
  · intro relations bound index
    exact (stage_fibre_generated readMaterial environment _ left right).mpr (relations bound index)

theorem successor_fibre_generated (runtime : LivingRuntimeState process)
    (left right : FormalCarrier R Value Var s) :
    successor readMaterial environment runtime ((completionMap readMaterial environment runtime).hom left) =
        successor readMaterial environment runtime ((completionMap readMaterial environment runtime).hom right) ↔
      ∀ bound (index : Fin (bound + 1)),
        liftMap (R := R) (left - right) ∈ LinearMap.range
          (stageRelationMap (R := R) (s := s) readMaterial environment
            ((materialHistory runtime.tick.next bound).stageAt index)) := by
  rw [successor_source, successor_source]
  exact completion_fibre_generated readMaterial environment runtime.tick.next left right

end
end SourceOperationRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
