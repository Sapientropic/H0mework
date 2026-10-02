import H0mework.Versions.R2.Realization.Operations.RuntimePrefix
import H0mework.Realization.ScalarCofinal.Tail

/-! The original runtime successor induces an action on its entire operation field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime

open SourceOperationEffects SourceGeneratedScalarCofinalNaturality CategoryTheory

noncomputable section

universe r u m n

variable {N : WorldRelationNetwork.{n}} {process : SourceNativeLivingRootProcess N}

theorem runtime_tail (runtime : LivingRuntimeState process) (index : Nat) :
    runtime.tick.next.advance index = runtime.advance (index + 1) := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change (runtime.tick.next.advance index).tick.next =
        (runtime.advance (index + 1)).tick.next
      rw [inductionHypothesis]

theorem tail_is_same_material_stage (runtime : LivingRuntimeState process)
    (bound : Nat) (index : Fin (bound + 1)) :
    HEq ((materialHistory runtime.tick.next bound).stageAt index)
      ((materialHistory runtime (bound + 1)).stageAt index.succ) := by
  dsimp [materialHistory, SourceGeneratedRuntimeMaterialHistoryAt.stageAt]
  rw [runtime_tail]

variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}

def dropFirst (bound : Nat) :
    PrefixCarrier Value s (bound + 1) →ₗ[R] PrefixCarrier Value s bound :=
  LinearMap.pi fun index => LinearMap.proj index.succ

theorem dropFirst_transition (bound : Nat) :
    (dropFirst (R := R) (Value := Value) (s := s) bound).comp (prefixRestriction (bound + 1)) =
      (prefixRestriction bound).comp (dropFirst (bound + 1)) := rfl

variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

theorem dropFirst_evaluator (runtime : LivingRuntimeState process) (bound : Nat) :
    (dropFirst (R := R) (s := s) bound).comp
        (prefixEvaluator readMaterial environment runtime (bound + 1)) =
      prefixEvaluator readMaterial environment runtime.tick.next bound := by
  apply LinearMap.ext
  intro word
  funext index
  change stageInventory readMaterial environment (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtime.advance (index.val + 1))) word =
    stageInventory readMaterial environment (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtime.tick.next.advance index.val)) word
  rw [runtime_tail]

def historyMorphism (runtime : LivingRuntimeState process) :
    Morphism
      (SourceGeneratedScalarCofinalTail.tail (prefixData (R := R) (s := s) readMaterial environment runtime))
      (prefixData (R := R) (s := s) readMaterial environment runtime.tick.next) where
  generatorMap := LinearMap.id
  stageMap := dropFirst
  transition_naturality := dropFirst_transition
  evaluator_naturality bound := dropFirst_evaluator (R := R) (s := s) readMaterial environment runtime bound

def successor (runtime : LivingRuntimeState process) :
    completion (R := R) (s := s) readMaterial environment runtime →ₗ[R]
      completion (R := R) (s := s) readMaterial environment runtime.tick.next :=
  ((historyMorphism (R := R) (s := s) readMaterial environment runtime).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (prefixData (R := R) (s := s) readMaterial environment runtime)
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime))
    (prefix_compatible (R := R) (s := s) readMaterial environment runtime.tick.next)).hom.comp
      (SourceGeneratedScalarCofinalTail.completionMap (prefixData (R := R) (s := s) readMaterial environment runtime)
        (prefix_compatible (R := R) (s := s) readMaterial environment runtime)).hom

theorem successor_source (runtime : LivingRuntimeState process) (word : FormalCarrier R Value Var s) :
    successor readMaterial environment runtime ((completionMap (R := R) (s := s) readMaterial environment runtime).hom word) =
      (completionMap (R := R) (s := s) readMaterial environment runtime.tick.next).hom word := by
  have tail := ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_source (prefixData (R := R) (s := s) readMaterial environment runtime)
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime)) word
  have source := ConcreteCategory.congr_hom
    ((historyMorphism (R := R) (s := s) readMaterial environment runtime).completionMorphism_source_naturality
      (SourceGeneratedScalarCofinalTail.compatible (prefixData (R := R) (s := s) readMaterial environment runtime)
        (prefix_compatible (R := R) (s := s) readMaterial environment runtime))
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime.tick.next)) word
  exact (congrArg ((historyMorphism (R := R) (s := s) readMaterial environment runtime).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (prefixData (R := R) (s := s) readMaterial environment runtime)
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime))
    (prefix_compatible (R := R) (s := s) readMaterial environment runtime.tick.next)).hom tail).trans source

theorem stageQuotient_reads_dropFirst (runtime : LivingRuntimeState process) (bound : Nat)
    (value : (SourceGeneratedScalarCofinalTail.tail
      (prefixData (R := R) (s := s) readMaterial environment runtime)).StageQuotient bound) :
    (prefixData (R := R) (s := s) readMaterial environment runtime.tick.next).stageRealization bound
        ((historyMorphism (R := R) (s := s) readMaterial environment runtime).stageQuotientMap bound value) =
      dropFirst (R := R) bound ((prefixData (R := R) (s := s) readMaterial environment runtime).stageRealization (bound + 1) value) := by
  obtain ⟨word, rfl⟩ := Submodule.mkQ_surjective
    ((SourceGeneratedScalarCofinalTail.tail (prefixData (R := R) (s := s) readMaterial environment runtime)).stageKernel bound) value
  exact (LinearMap.congr_fun (dropFirst_evaluator (R := R) (s := s) readMaterial environment runtime bound) word).symm

theorem successor_reads_dropFirst (runtime : LivingRuntimeState process) (bound : Nat)
    (value : completion (R := R) (s := s) readMaterial environment runtime) :
    stageRead (R := R) (s := s) readMaterial environment runtime.tick.next bound (successor readMaterial environment runtime value) =
      dropFirst (R := R) bound (stageRead (R := R) (s := s) readMaterial environment runtime (bound + 1) value) := by
  have afterMorphism := ConcreteCategory.congr_hom
    ((historyMorphism (R := R) (s := s) readMaterial environment runtime).completionMorphism_restriction
      (SourceGeneratedScalarCofinalTail.compatible (prefixData (R := R) (s := s) readMaterial environment runtime)
        (prefix_compatible (R := R) (s := s) readMaterial environment runtime))
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime.tick.next) bound)
    ((SourceGeneratedScalarCofinalTail.completionMap (prefixData (R := R) (s := s) readMaterial environment runtime)
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime)).hom value)
  have afterTail := ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_restriction (prefixData (R := R) (s := s) readMaterial environment runtime)
      (prefix_compatible (R := R) (s := s) readMaterial environment runtime) bound) value
  exact (congrArg ((prefixData (R := R) (s := s) readMaterial environment runtime.tick.next).stageRealization bound) afterMorphism).trans
    ((congrArg (fun quotient => (prefixData (R := R) (s := s) readMaterial environment runtime.tick.next).stageRealization bound
      ((historyMorphism (R := R) (s := s) readMaterial environment runtime).stageQuotientMap bound quotient)) afterTail).trans
      (stageQuotient_reads_dropFirst readMaterial environment runtime bound
        (((prefixData (R := R) (s := s) readMaterial environment runtime).restriction
          (prefix_compatible (R := R) (s := s) readMaterial environment runtime) (bound + 1)).hom value)))

end
end SourceOperationRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
