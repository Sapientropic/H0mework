import H0mework.Realization.Operations.RuntimeSuccessor

/-! The source operation update holds on every point of the generated completion. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime

open SourceOperationEffects SourceOperationScalarRelations
open SourceGeneratedScalarCofinalKernelCompletion CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u m n

variable {N : WorldRelationNetwork.{n}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

theorem stageInventory_next_old {runtime : LivingRuntimeState process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) (word : FormalCarrier R Value Var s) :
    (stageInventory readMaterial environment
        (SourceGeneratedRuntimeMaterialStageAt.generate stage.next) word).1 =
      (stageInventory readMaterial environment stage word).1 +
        (stageInventory readMaterial environment stage word).2 := by
  have generated := LinearMap.congr_fun
    (evaluation_update (R := R) (s := s)
      (oldEnvironment readMaterial environment stage)
      (incrementEnvironment readMaterial environment stage)) word
  have environmentUpdate : oldEnvironment readMaterial environment stage +
      incrementEnvironment readMaterial environment stage = environment (readMaterial stage.next.state) := by
    unfold oldEnvironment incrementEnvironment
    rw [← map_add]
    congr 1
    abel
  rw [environmentUpdate] at generated
  exact generated

private theorem prefixQuotient_next_old (runtime : LivingRuntimeState process) (bound : Nat)
    (value : (prefixData (R := R) (s := s) readMaterial environment runtime).StageQuotient (bound + 1))
    (index : Fin (bound + 1)) :
    ((prefixData (R := R) (s := s) readMaterial environment runtime).stageRealization (bound + 1) value index.succ).1 =
      ((prefixData (R := R) (s := s) readMaterial environment runtime).stageRealization bound
        ((prefixData (R := R) (s := s) readMaterial environment runtime).quotientTransition
          (prefix_compatible readMaterial environment runtime) bound value) index).1 +
      ((prefixData (R := R) (s := s) readMaterial environment runtime).stageRealization bound
        ((prefixData (R := R) (s := s) readMaterial environment runtime).quotientTransition
          (prefix_compatible readMaterial environment runtime) bound value) index).2 := by
  obtain ⟨word, rfl⟩ := Submodule.mkQ_surjective
    ((prefixData (R := R) (s := s) readMaterial environment runtime).stageKernel (bound + 1)) value
  change (stageInventory readMaterial environment (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtime.advance (index.val + 1))) word).1 =
    (stageInventory readMaterial environment (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtime.advance index.val)) word).1 +
    (stageInventory readMaterial environment (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtime.advance index.val)) word).2
  exact stageInventory_next_old readMaterial environment
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance index.val)) word

theorem stageRead_next_old (runtime : LivingRuntimeState process) (bound : Nat)
    (value : completion (R := R) (s := s) readMaterial environment runtime) (index : Fin (bound + 1)) :
    (stageRead (R := R) (s := s) readMaterial environment runtime (bound + 1) value index.succ).1 =
      (stageRead (R := R) (s := s) readMaterial environment runtime bound value index).1 +
        (stageRead (R := R) (s := s) readMaterial environment runtime bound value index).2 := by
  have restriction := limit.w
    ((prefixData (R := R) (s := s) readMaterial environment runtime).quotientTower
      (prefix_compatible readMaterial environment runtime))
    (homOfLE (Nat.le_succ bound)).op
  simp only [Data.quotientTower, Functor.ofOpSequence_map_homOfLE_succ] at restriction
  change (prefixData (R := R) (s := s) readMaterial environment runtime).restriction
        (prefix_compatible readMaterial environment runtime) (bound + 1) ≫
      ModuleCat.ofHom ((prefixData (R := R) (s := s) readMaterial environment runtime).quotientTransition
        (prefix_compatible readMaterial environment runtime) bound) =
    (prefixData (R := R) (s := s) readMaterial environment runtime).restriction
      (prefix_compatible readMaterial environment runtime) bound at restriction
  have atValue := ConcreteCategory.congr_hom restriction value
  have generated := prefixQuotient_next_old readMaterial environment runtime bound
    (((prefixData (R := R) (s := s) readMaterial environment runtime).restriction
      (prefix_compatible readMaterial environment runtime) (bound + 1)).hom value) index
  change (prefixData (R := R) (s := s) readMaterial environment runtime).quotientTransition
      (prefix_compatible readMaterial environment runtime) bound
      (((prefixData (R := R) (s := s) readMaterial environment runtime).restriction
        (prefix_compatible readMaterial environment runtime) (bound + 1)).hom value) =
    ((prefixData (R := R) (s := s) readMaterial environment runtime).restriction
      (prefix_compatible readMaterial environment runtime) bound).hom value at atValue
  rw [atValue] at generated
  exact generated

theorem successor_old_eq_old_add_effect (runtime : LivingRuntimeState process) (bound : Nat)
    (value : completion (R := R) (s := s) readMaterial environment runtime) (index : Fin (bound + 1)) :
    (stageRead (R := R) (s := s) readMaterial environment runtime.tick.next bound
        (successor readMaterial environment runtime value) index).1 =
      (stageRead (R := R) (s := s) readMaterial environment runtime bound value index).1 +
        (stageRead (R := R) (s := s) readMaterial environment runtime bound value index).2 := by
  rw [successor_reads_dropFirst]
  exact stageRead_next_old readMaterial environment runtime bound value index

end
end SourceOperationRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
