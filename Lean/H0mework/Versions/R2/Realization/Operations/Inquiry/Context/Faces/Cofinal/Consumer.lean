import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Cofinal.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.History.Consumer

/-! Independent prefix reads recover the source-held relation programme
through its faithful character image. The logical fibre preserves the full
word, and every read remains attached to the original runtime receipt. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Cofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceOperationScalarInventoryLift
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

def relationAt (count : Nat) : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort) :=
  relationMap (R := ℤ) (readEnv runtime source (runtime.stateAt count))
    (relationWords runtime source (runtime.stateAt count))

def relationField (count : Nat) := sourceMap runtime source count (relationAt runtime source count)

theorem relation_read (count bound : Nat) (index : Fin (bound + 1)) :
    read runtime source count bound (relationField runtime source count) index =
      History.stageInventory runtime source (count + index.val) (relationAt runtime source count) :=
  read_source runtime source count bound (relationAt runtime source count) index

theorem relation_zero_iff (count : Nat) : relationField runtime source count = 0 ↔
    ∀ bound (index : Fin (bound + 1)),
      History.stageInventory runtime source (count + index.val) (relationAt runtime source count) = 0 := by
  constructor
  · intro zero bound index
    have atStage := congrArg (fun value => read runtime source count bound value index) zero
    rw [relation_read, map_zero, Pi.zero_apply] at atStage
    exact atStage
  · intro zero
    have same : (H.sourceMap runtime source count).hom (relationAt runtime source count) = 0 := by
      have fibre := (History.fibre runtime source count (relationAt runtime source count) 0).mpr
        (fun bound index => (zero bound index).trans (map_zero _).symm)
      exact fibre.trans (map_zero _)
    exact (congrArg (E.canonicalMap ℤ (H.completion runtime source count)) same).trans
      (map_zero _)

theorem relation_next_read (count bound : Nat) (index : Fin (bound + 1)) :
    read runtime source (count + 1) bound (next runtime source count (relationField runtime source count)) index =
      History.stageInventory runtime source (count + 1 + index.val) (relationAt runtime source count) := by
  rw [relationField, next_source]
  exact read_source runtime source (count + 1) bound (relationAt runtime source count) index

def relationWitness (count : Nat) : SourceOperationLogic.Fibre (sourceMap runtime source count)
    (SourceOperationLogic.q (sourceMap runtime source count) (relationAt runtime source count)) :=
  SourceOperationLogic.sourceWitness _ _

theorem complete_word_readback (count : Nat) :
    (fibreDecomposition runtime source count).symm
      ⟨SourceOperationLogic.q (sourceMap runtime source count) (relationAt runtime source count),
        relationWitness runtime source count⟩ = relationAt runtime source count := rfl

variable (initial : History.C.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

theorem actual_source_read (offset bound : Nat)
    (word : H.Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (index : Fin (bound + 1)) :
    read (History.C.runtime initial) (History.actualSource initial) offset bound
      (sourceMap (History.C.runtime initial) (History.actualSource initial) offset word) index =
      updateInventory (R := ℤ)
        (History.C.frames initial (offset + index.val)).rawRead.environment
        ((History.C.frames initial (offset + index.val + 1)).rawRead.environment -
          (History.C.frames initial (offset + index.val)).rawRead.environment) word :=
  (read_source (History.C.runtime initial) (History.actualSource initial) offset bound word index).trans
    (LinearMap.congr_fun (History.actual_stage initial (offset + index.val)) word)

theorem actual_receipt (count : Nat) : type_of% (History.stage_receipt runtime count) :=
  History.stage_receipt runtime count

end SourceOperationInquiry.Context.Faces.Cofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
