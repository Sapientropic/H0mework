import H0mework.Versions.Rc19e94a5.SecondEdition.SaturationMonoid.GenericFoundation.Operations.Native.Substitution.Source

/-! The source-generated diagram acts on the whole cofinal completion, then
uses the existing faithful character map. No inverse or chosen action is input. -/

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

def diagram (runtime : LivingRuntimeState process) :
    SourceGeneratedScalarCofinalNaturality.Morphism
      (prefixData (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime.tick.next)
      (prefixData (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime) where
  generatorMap := words process
  stageMap := fun _ => LinearMap.id
  transition_naturality := fun _ => by simp only [LinearMap.id_comp, LinearMap.comp_id]; rfl
  evaluator_naturality := fun bound => by
    rw [LinearMap.id_comp]
    exact (prefix_square runtime bound).symm

def returnToCurrent (runtime : LivingRuntimeState process) :
    completion (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime.tick.next →ₗ[ℤ]
      completion (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime :=
  ((diagram runtime).completionMorphism
    (prefix_compatible (statePoint process) (Field.environment process) runtime.tick.next)
    (prefix_compatible (statePoint process) (Field.environment process) runtime)).hom

def action (runtime : LivingRuntimeState process) :
    completion (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime →ₗ[ℤ]
      completion (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime :=
  (returnToCurrent runtime).comp (successor (statePoint process) (Field.environment process) runtime)

theorem return_source (runtime : LivingRuntimeState process) (word : Word process) :
    returnToCurrent runtime ((completionMap (R := ℤ) (s := PUnit.unit)
      (statePoint process) (Field.environment process) runtime.tick.next).hom word) =
    (completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom (words process word) := by
  exact ConcreteCategory.congr_hom ((diagram runtime).completionMorphism_source_naturality
    (prefix_compatible (statePoint process) (Field.environment process) runtime.tick.next)
    (prefix_compatible (statePoint process) (Field.environment process) runtime)) word

theorem action_source (runtime : LivingRuntimeState process) (word : Word process) :
    action runtime ((completionMap (R := ℤ) (s := PUnit.unit)
      (statePoint process) (Field.environment process) runtime).hom word) =
    (completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom (words process word) := by
  change returnToCurrent runtime (successor (statePoint process) (Field.environment process) runtime
    ((completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom word)) = _
  rw [successor_source]
  exact return_source runtime word

def characterAction (runtime : LivingRuntimeState process) :
    Character.Carrier (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime →ₗ[ℤ]
      Character.Carrier (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime :=
  SourceGeneratedScalarCharacterExact.map (action runtime)

theorem character_action_source (runtime : LivingRuntimeState process) (word : Word process) :
    characterAction runtime (Character.sourceMap (R := ℤ) (s := PUnit.unit)
      (statePoint process) (Field.environment process) runtime word) =
    Character.sourceMap (R := ℤ) (s := PUnit.unit) (statePoint process)
      (Field.environment process) runtime (words process word) := by
  exact (SourceGeneratedScalarCharacterExact.map_canonicalMap (action runtime)
    ((completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom word)).trans
      (congrArg (Character.fieldMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime)
        (action_source runtime word))

end
end SourceOperationNative.Substitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
