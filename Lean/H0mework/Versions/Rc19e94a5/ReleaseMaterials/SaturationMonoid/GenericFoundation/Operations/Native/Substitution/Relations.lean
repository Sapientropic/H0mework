import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Substitution.Field

/-! The actual syntax action preserves the full field kernel and all original
generated old/effect relation ranges. Its differential square is source-generated. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Substitution
open SourceOperationEffects SourceOperationScalarRelations SourceOperationRuntime
open SourceGeneratedScalarCofinalKernelCompletion SourceGeneratedScalarCofinalNaturality
open CategoryTheory
noncomputable section
universe u
variable {N : WorldRelationNetwork.{u}} (process : SourceNativeLivingRootProcess N)

variable {process}

def differentialMorphism (runtime : LivingRuntimeState process) :
    SourceGeneratedScalarDifferentialResidual.Morphism
      (completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom
      (completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom where
  sourceMap := words process
  targetMap := action runtime
  commutes := by
    apply LinearMap.ext
    intro word
    exact action_source runtime word

theorem kernel_preserved (runtime : LivingRuntimeState process) (word : Word process)
    (invisible : (completionMap (R := ℤ) (s := PUnit.unit)
      (statePoint process) (Field.environment process) runtime).hom word = 0) :
    (completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom
      (words process word) = 0 :=
  (action_source runtime word).symm.trans
    ((congrArg (action runtime) invisible).trans (map_zero (action runtime)))

theorem stage_relation_iff (runtime : LivingRuntimeState process) (word : Word process) :
    SourceOperationScalarInventoryLift.liftMap (R := ℤ) (words process word) ∈
      LinearMap.range (stageRelationMap (R := ℤ) (s := PUnit.unit) (statePoint process)
        (Field.environment process) (SourceGeneratedRuntimeMaterialStageAt.generate runtime)) ↔
    SourceOperationScalarInventoryLift.liftMap (R := ℤ) word ∈
      LinearMap.range (stageRelationMap (R := ℤ) (s := PUnit.unit) (statePoint process)
        (Field.environment process) (SourceGeneratedRuntimeMaterialStageAt.generate runtime.tick.next)) := by
  have current := stage_fibre_generated (R := ℤ) (s := PUnit.unit) (statePoint process)
    (Field.environment process) (SourceGeneratedRuntimeMaterialStageAt.generate runtime) (words process word) 0
  have next := stage_fibre_generated (R := ℤ) (s := PUnit.unit) (statePoint process)
    (Field.environment process) (SourceGeneratedRuntimeMaterialStageAt.generate runtime.tick.next) word 0
  simp only [map_zero, sub_zero] at current next
  exact current.symm.trans ((Eq.to_iff (congrArg (fun value => value = 0) (stage_pair runtime word))).trans next)

theorem whole_relation_ranges_preserved (runtime : LivingRuntimeState process) (word : Word process)
    (generated : ∀ bound (index : Fin (bound + 1)),
      SourceOperationScalarInventoryLift.liftMap (R := ℤ) word ∈
        LinearMap.range (stageRelationMap (R := ℤ) (s := PUnit.unit)
          (statePoint process) (Field.environment process) ((materialHistory runtime bound).stageAt index))) :
    ∀ bound (index : Fin (bound + 1)),
      SourceOperationScalarInventoryLift.liftMap (R := ℤ) (words process word) ∈
        LinearMap.range (stageRelationMap (R := ℤ) (s := PUnit.unit)
          (statePoint process) (Field.environment process) ((materialHistory runtime bound).stageAt index)) := by
  have current := completion_fibre_generated (R := ℤ) (s := PUnit.unit) (statePoint process)
    (Field.environment process) runtime word 0
  simp only [map_zero, sub_zero] at current
  have invisible := kernel_preserved runtime word (current.mpr generated)
  have moved := completion_fibre_generated (R := ℤ) (s := PUnit.unit) (statePoint process)
    (Field.environment process) runtime (words process word) 0
  simp only [map_zero, sub_zero] at moved
  exact moved.mp invisible

end
end SourceOperationNative.Substitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
