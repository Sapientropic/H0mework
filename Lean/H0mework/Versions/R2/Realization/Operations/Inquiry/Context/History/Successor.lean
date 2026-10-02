import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.History.Source
import H0mework.Realization.ScalarCofinal.Tail

/-! The next operation history is the original runtime's next offset. The
existing tail and naturality producers transport its whole cofinal fibre. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.History
open RootInquiryCompletion SourceOperationEffects
open SourceGeneratedScalarCofinalNaturality CategoryTheory

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

def dropFirst (bound : Nat) : Prefix (PhysicalValue := PhysicalValue) (sort := sort) (bound + 1) →ₗ[ℤ]
    Prefix (PhysicalValue := PhysicalValue) (sort := sort) bound :=
  LinearMap.pi fun index => LinearMap.proj index.succ

theorem dropFirst_transition (bound : Nat) :
    (dropFirst (PhysicalValue := PhysicalValue) (sort := sort) bound).comp (restriction (bound + 1)) =
      (restriction bound).comp (dropFirst (PhysicalValue := PhysicalValue) (sort := sort) (bound + 1)) := rfl

theorem dropFirst_evaluator (offset bound : Nat) :
    (dropFirst (PhysicalValue := PhysicalValue) (sort := sort) bound).comp
      (prefixEvaluator runtime source offset (bound + 1)) =
        prefixEvaluator runtime source (offset + 1) bound := by
  apply LinearMap.ext
  intro word
  funext index
  change stageInventory runtime source (offset + (index.val + 1)) word =
    stageInventory runtime source (offset + 1 + index.val) word
  rw [← Nat.add_assoc, Nat.add_right_comm offset index.val 1]

def historyMorphism (offset : Nat) :
    Morphism (SourceGeneratedScalarCofinalTail.tail (data runtime source offset))
      (data runtime source (offset + 1)) where
  generatorMap := LinearMap.id
  stageMap := dropFirst
  transition_naturality := dropFirst_transition
  evaluator_naturality := dropFirst_evaluator runtime source offset

def successor (offset : Nat) : completion runtime source offset →ₗ[ℤ]
    completion runtime source (offset + 1) :=
  ((historyMorphism runtime source offset).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (data runtime source offset) (compatible runtime source offset))
    (compatible runtime source (offset + 1))).hom.comp
      (SourceGeneratedScalarCofinalTail.completionMap (data runtime source offset) (compatible runtime source offset)).hom

theorem successor_source (offset : Nat)
    (word : Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    successor runtime source offset ((sourceMap runtime source offset).hom word) =
      (sourceMap runtime source (offset + 1)).hom word := by
  have tail := ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_source
      (data runtime source offset) (compatible runtime source offset)) word
  have square := ConcreteCategory.congr_hom
    ((historyMorphism runtime source offset).completionMorphism_source_naturality
      (SourceGeneratedScalarCofinalTail.compatible (data runtime source offset) (compatible runtime source offset))
      (compatible runtime source (offset + 1))) word
  exact (congrArg ((historyMorphism runtime source offset).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (data runtime source offset) (compatible runtime source offset))
    (compatible runtime source (offset + 1))).hom tail).trans square

theorem successor_stage (offset bound : Nat)
    (word : Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (index : Fin (bound + 1)) :
    readPrefix runtime source (offset + 1) bound
      (successor runtime source offset ((sourceMap runtime source offset).hom word)) index =
        stageInventory runtime source (offset + 1 + index.val) word := by
  rw [successor_source]
  exact source_stage runtime source (offset + 1) bound word index

theorem successor_fibre_generated (offset : Nat)
    (left right : Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    successor runtime source offset ((sourceMap runtime source offset).hom left) =
        successor runtime source offset ((sourceMap runtime source offset).hom right) ↔
      ∀ bound (index : Fin (bound + 1)),
        SourceOperationScalarInventoryLift.liftMap (R := ℤ) (left - right) ∈ LinearMap.range
          (SourceOperationScalarPresentation.relationMap (R := ℤ)
            (pairEnvironmentAt runtime source (runtime.stateAt (offset + 1 + index.val)))) := by
  rw [successor_source, successor_source]
  exact fibre_generated runtime source (offset + 1) left right

end SourceOperationInquiry.Context.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
