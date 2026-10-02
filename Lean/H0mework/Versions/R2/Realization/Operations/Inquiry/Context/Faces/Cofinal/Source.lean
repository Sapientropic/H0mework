import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.History.Successor
import H0mework.Realization.Integral.CharacterExact
import H0mework.Realization.Logic.SourceScope

/-! The whole actual operation history enters the existing faithful
character image. The logical fibre retains every original operation word;
the next character map consumes the original history successor. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Cofinal
open RootInquiryCompletion SourceOperationEffects
namespace H
export SourceOperationInquiry.Context.History
  (Words Prefix completion sourceMap readPrefix successor successor_source source_stage fibre_generated)
end H
namespace E
export SourceGeneratedScalarCharacterExact
  (Carrier canonicalMap canonicalMap_injective equiv factor factor_canonicalMap map map_canonicalMap)
end E
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

abbrev Carrier (offset : Nat) := E.Carrier ℤ (H.completion runtime source offset)

def sourceMap (offset : Nat) : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort) →ₗ[ℤ] Carrier runtime source offset :=
  (E.canonicalMap ℤ (H.completion runtime source offset)).comp (H.sourceMap runtime source offset).hom

def read (offset bound : Nat) : Carrier runtime source offset →ₗ[ℤ]
    H.Prefix (PhysicalValue := PhysicalValue) (sort := sort) bound :=
  E.factor (H.readPrefix runtime source offset bound)

theorem read_source (offset bound : Nat)
    (word : H.Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (index : Fin (bound + 1)) :
    read runtime source offset bound (sourceMap runtime source offset word) index =
      History.stageInventory runtime source (offset + index.val) word := by
  have square := LinearMap.congr_fun (E.factor_canonicalMap (H.readPrefix runtime source offset bound))
    ((H.sourceMap runtime source offset).hom word)
  exact (congrFun square index).trans (H.source_stage runtime source offset bound word index)

theorem source_fibre (offset : Nat)
    (left right : H.Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    sourceMap runtime source offset left = sourceMap runtime source offset right ↔
      ∀ bound (index : Fin (bound + 1)),
        SourceOperationScalarInventoryLift.liftMap (R := ℤ) (left - right) ∈ LinearMap.range
          (SourceOperationScalarPresentation.relationMap (R := ℤ)
            (pairEnvironmentAt runtime source (runtime.stateAt (offset + index.val)))) := by
  constructor
  · intro same
    exact (H.fibre_generated runtime source offset left right).mp
      (E.canonicalMap_injective ℤ (H.completion runtime source offset) same)
  · intro same
    exact congrArg (E.canonicalMap ℤ (H.completion runtime source offset))
      ((H.fibre_generated runtime source offset left right).mpr same)

def next (offset : Nat) : Carrier runtime source offset →ₗ[ℤ] Carrier runtime source (offset + 1) :=
  E.map (H.successor runtime source offset)

theorem next_source (offset : Nat)
    (word : H.Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    next runtime source offset (sourceMap runtime source offset word) =
      sourceMap runtime source (offset + 1) word := by
  exact (E.map_canonicalMap (H.successor runtime source offset)
    ((H.sourceMap runtime source offset).hom word)).trans
      (congrArg (E.canonicalMap ℤ (H.completion runtime source (offset + 1)))
        (H.successor_source runtime source offset word))

def fibreDecomposition (offset : Nat) := SourceOperationLogic.fibreDecomposition (sourceMap runtime source offset)

end SourceOperationInquiry.Context.Faces.Cofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
