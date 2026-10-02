import H0mework.Realization.Integral.CharacterExact
import H0mework.Versions.R2.Realization.Operations.RuntimeEvolution
import H0mework.Versions.R2.Realization.Operations.RuntimeRelations

/-! The complete operation field enters the existing faithful character image with its original scalar action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime.Character

open SourceOperationEffects SourceOperationScalarInventoryLift

noncomputable section

universe r u m n

variable {N : WorldRelationNetwork.{n}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

abbrev Carrier (runtime : LivingRuntimeState process) :=
  SourceGeneratedScalarCharacterExact.Carrier R
    (completion (R := R) (s := s) readMaterial environment runtime)

def fieldMap (runtime : LivingRuntimeState process) :
    completion (R := R) (s := s) readMaterial environment runtime →ₗ[R]
      Carrier (R := R) (s := s) readMaterial environment runtime :=
  SourceGeneratedScalarCharacterExact.canonicalMap R _

def sourceMap (runtime : LivingRuntimeState process) :
    FormalCarrier R Value Var s →ₗ[R] Carrier (R := R) (s := s) readMaterial environment runtime :=
  (fieldMap readMaterial environment runtime).comp (completionMap readMaterial environment runtime).hom

def stageRead (runtime : LivingRuntimeState process) (bound : Nat) :
    Carrier (R := R) (s := s) readMaterial environment runtime →ₗ[R] PrefixCarrier Value s bound :=
  SourceGeneratedScalarCharacterExact.factor
    (SourceOperationRuntime.stageRead (R := R) (s := s) readMaterial environment runtime bound)

theorem stageRead_fieldMap (runtime : LivingRuntimeState process) (bound : Nat)
    (value : completion (R := R) (s := s) readMaterial environment runtime) :
    stageRead readMaterial environment runtime bound (fieldMap readMaterial environment runtime value) =
      SourceOperationRuntime.stageRead readMaterial environment runtime bound value :=
  LinearMap.congr_fun (SourceGeneratedScalarCharacterExact.factor_canonicalMap
    (SourceOperationRuntime.stageRead (R := R) (s := s) readMaterial environment runtime bound)) value

theorem source_reads_actual_stage (runtime : LivingRuntimeState process) (bound : Nat)
    (word : FormalCarrier R Value Var s) (index : Fin (bound + 1)) :
    stageRead readMaterial environment runtime bound (sourceMap readMaterial environment runtime word) index =
      stageInventory readMaterial environment ((materialHistory runtime bound).stageAt index) word :=
  (congrFun (stageRead_fieldMap readMaterial environment runtime bound
    ((completionMap readMaterial environment runtime).hom word)) index).trans
      (completion_source_to_actual_stage readMaterial environment runtime bound word index)

def successor (runtime : LivingRuntimeState process) :
    Carrier (R := R) (s := s) readMaterial environment runtime →ₗ[R]
      Carrier (R := R) (s := s) readMaterial environment runtime.tick.next :=
  SourceGeneratedScalarCharacterExact.map
    (SourceOperationRuntime.successor (R := R) (s := s) readMaterial environment runtime)

theorem successor_fieldMap (runtime : LivingRuntimeState process)
    (value : completion (R := R) (s := s) readMaterial environment runtime) :
    successor readMaterial environment runtime (fieldMap readMaterial environment runtime value) =
      fieldMap readMaterial environment runtime.tick.next
        (SourceOperationRuntime.successor readMaterial environment runtime value) :=
  SourceGeneratedScalarCharacterExact.map_canonicalMap
    (SourceOperationRuntime.successor (R := R) (s := s) readMaterial environment runtime) value

theorem successor_source (runtime : LivingRuntimeState process) (word : FormalCarrier R Value Var s) :
    successor readMaterial environment runtime (sourceMap readMaterial environment runtime word) =
      sourceMap readMaterial environment runtime.tick.next word := by
  exact (successor_fieldMap readMaterial environment runtime
    ((completionMap readMaterial environment runtime).hom word)).trans
      (congrArg (fieldMap readMaterial environment runtime.tick.next)
        (SourceOperationRuntime.successor_source readMaterial environment runtime word))

theorem successor_equation (runtime : LivingRuntimeState process) (bound : Nat)
    (value : Carrier (R := R) (s := s) readMaterial environment runtime) (index : Fin (bound + 1)) :
    (stageRead readMaterial environment runtime.tick.next bound
      (successor readMaterial environment runtime value) index).1 =
      (stageRead readMaterial environment runtime bound value index).1 +
        (stageRead readMaterial environment runtime bound value index).2 := by
  obtain ⟨completed, rfl⟩ := SourceGeneratedScalarCharacterExact.canonicalMap_surjective R
    (completion (R := R) (s := s) readMaterial environment runtime) value
  change (stageRead readMaterial environment runtime.tick.next bound
      (successor readMaterial environment runtime (fieldMap readMaterial environment runtime completed)) index).1 = _
  rw [successor_fieldMap, stageRead_fieldMap]
  change _ = (stageRead readMaterial environment runtime bound
    (fieldMap readMaterial environment runtime completed) index).1 +
      (stageRead readMaterial environment runtime bound
        (fieldMap readMaterial environment runtime completed) index).2
  rw [stageRead_fieldMap]
  exact successor_old_eq_old_add_effect readMaterial environment runtime bound completed index

theorem source_fibre_generated (runtime : LivingRuntimeState process)
    (left right : FormalCarrier R Value Var s) :
    sourceMap readMaterial environment runtime left = sourceMap readMaterial environment runtime right ↔
      ∀ bound (index : Fin (bound + 1)),
        liftMap (R := R) (left - right) ∈ LinearMap.range
          (stageRelationMap (R := R) (s := s) readMaterial environment
            ((materialHistory runtime bound).stageAt index)) := by
  constructor
  · intro same
    exact (completion_fibre_generated readMaterial environment runtime left right).mp
      (SourceGeneratedScalarCharacterExact.canonicalMap_injective R
        (completion (R := R) (s := s) readMaterial environment runtime) same)
  · intro relations
    exact congrArg (fieldMap readMaterial environment runtime)
      ((completion_fibre_generated readMaterial environment runtime left right).mpr relations)

end
end SourceOperationRuntime.Character
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
