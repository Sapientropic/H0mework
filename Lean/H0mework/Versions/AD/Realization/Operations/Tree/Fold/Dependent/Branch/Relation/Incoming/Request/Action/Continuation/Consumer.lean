import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action.Continuation.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action.Continuation
open RootInquiryCompletion RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (word : Word root visit recognition)
theorem all_original_seed : ∀ atom ∈ (combinedSeed root visit recognition count).trace,
    atom ∈ (seed root visit recognition count word).trace := (SourceHistoryCommon.parallel_left _ _ _).1

theorem all_actual_trace : ∀ atom ∈
    (RootGeneratedDebtActivationJointSource.OwnerFree.Relations.exposure
      (sourceRoot root visit recognition count word).toAuthoritativeRoot (queryVisit root visit recognition count).current
      (reader root visit recognition count word) (paid root visit recognition count word)).trace,
    atom ∈ (seed root visit recognition count word).trace := (SourceHistoryCommon.parallel_right _ _ _).1

theorem actual_current : (frame root visit recognition count U7 calculus word).old.visit.current =
    RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent
      (sourceRoot root visit recognition count word).toAuthoritativeRoot (queryVisit root visit recognition count).current
      (reader root visit recognition count word) (paid root visit recognition count word) := by
  have depth := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime_depth
    (sourceRoot root visit recognition count word).toAuthoritativeRoot (queryVisit root visit recognition count).current
    (reader root visit recognition count word) (endpoint root visit recognition count word)
  exact congrArg (fun index => (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit
    (sourceRoot root visit recognition count word).toAuthoritativeRoot (queryVisit root visit recognition count).current
    (reader root visit recognition count word) index).current) depth.symm

theorem initial_source : ∀ atom ∈ (seed root visit recognition count word).trace,
    atom ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.sourceFace
      (seed root visit recognition count word) (frame root visit recognition count U7 calculus word)).rootRead.1.1.1.1.2.1.trace :=
  by
    intro atom belongs
    change atom ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.updatedSeed
      (seed root visit recognition count word) (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame root visit recognition count U7 calculus word))
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root visit recognition count U7 calculus word))).trace
    apply (SourceHistoryCommon.parallel_left _ _ _).1
    unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.priorSeed
    generalize (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame root visit recognition count U7 calculus word)).inventory = stored
    cases stored with
    | none => exact belongs
    | some carried => exact (SourceHistoryCommon.parallel_left (seed root visit recognition count word).root
        (seed root visit recognition count word) carried).1 atom belongs

theorem actual_query (index : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.queryAt
      (seed root visit recognition count word) (frame root visit recognition count U7 calculus word) index) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.queryAt _ _ index

theorem actual_next (index : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.nextAt
      (seed root visit recognition count word) (frame root visit recognition count U7 calculus word) index) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.nextAt _ _ index

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
