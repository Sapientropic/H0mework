import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
  (actual_query actual_input completed_value paid_history actual_next actual_answer born_inventory)
end A
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (updatedSeed supplied_seed_preserved)
end P
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

theorem actual_initial : (runtime root visit recognition U7 calculus count).initialState.engine.node =
    .active (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
      (initial root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus count)) := rfl
theorem exact_source : (initialRoot root visit recognition U7 calculus count).source.base.restructuringSource =
    (SourceGeneratedInquiryReceiptAction.targetState (Born.sourceFrame root visit recognition U7 calculus count)
      (Born.configuration root visit recognition U7 calculus)).root.source.base.restructuringSource := rfl
theorem exact_ledger : (initialRoot root visit recognition U7 calculus count).toAuthoritativeRoot.toLedgerRoot =
    (SourceGeneratedInquiryReceiptAction.targetState (Born.sourceFrame root visit recognition U7 calculus count)
      (Born.configuration root visit recognition U7 calculus)).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem exact_visit : initialVisit root visit recognition U7 calculus count =
    (SourceGeneratedInquiryReceiptAction.targetState (Born.sourceFrame root visit recognition U7 calculus count)
      (Born.configuration root visit recognition U7 calculus)).visit := rfl
theorem exact_occurrence : (initialRoot root visit recognition U7 calculus count).emitted
    (initialVisit root visit recognition U7 calculus count).current =
    (SourceGeneratedInquiryReceiptAction.targetState (Born.sourceFrame root visit recognition U7 calculus count)
      (Born.configuration root visit recognition U7 calculus)).root.emitted
        (SourceGeneratedInquiryReceiptAction.targetState (Born.sourceFrame root visit recognition U7 calculus count)
          (Born.configuration root visit recognition U7 calculus)).visit.current := rfl
theorem old_projection (projection : (initial root visit recognition U7 calculus count).currentState.root.source.base.projectionLaw.Projection) :
    type_of% ((oldInstallation root visit recognition U7 calculus count).outcome_heq
      (E.Shared.actualOccurrence (initial root visit recognition U7 calculus count)) projection) :=
  (oldInstallation root visit recognition U7 calculus count).outcome_heq
    (E.Shared.actualOccurrence (initial root visit recognition U7 calculus count)) projection

theorem stock_preserved (stage : Nat) (event) (present : event ∈ (Born.stock root visit recognition U7 calculus count).trace) :
    event ∈ (materialFace root visit recognition U7 calculus count stage).rootRead.1.1.1.1.2.1.trace := by
  change event ∈ (P.updatedSeed (seed root visit recognition U7 calculus count)
    (E.epoch (frameAt root visit recognition U7 calculus count stage))
    (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus count stage))).trace
  have inSeed : event ∈ (seed root visit recognition U7 calculus count).trace :=
    (SourceHistoryCommon.parallel_left _ _ _).1 event present
  exact P.supplied_seed_preserved (seed root visit recognition U7 calculus count)
    (frameAt root visit recognition U7 calculus count stage) event inSeed
theorem actual_disposition (stage : Nat) : (materialFace root visit recognition U7 calculus count stage).rootRead.1.2.2.2.1 =
    SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.disposition
      (seed root visit recognition U7 calculus count) (E.epoch (frameAt root visit recognition U7 calculus count stage))
      (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus count stage)) := rfl
theorem actual_query (stage : Nat) : type_of% (A.actual_query (seed root visit recognition U7 calculus count)
    (frameAt root visit recognition U7 calculus count stage)) := A.actual_query _ _
theorem actual_input (stage : Nat) : type_of% (A.actual_input (seed root visit recognition U7 calculus count)
    (initial root visit recognition U7 calculus count) stage) := A.actual_input _ _ stage
theorem actual_result (stage : Nat) : type_of% (A.completed_value (seed root visit recognition U7 calculus count)
    (frameAt root visit recognition U7 calculus count stage)) := A.completed_value _ _
theorem paid_trace (stage : Nat) : type_of% (A.paid_history (seed root visit recognition U7 calculus count)
    (frameAt root visit recognition U7 calculus count stage)) := A.paid_history _ _
theorem actual_next (stage : Nat) : type_of% (A.actual_next (seed root visit recognition U7 calculus count)
    (initial root visit recognition U7 calculus count) stage) := A.actual_next _ _ stage
theorem actual_answer (stage : Nat) : type_of% (A.actual_answer (seed root visit recognition U7 calculus count)
    (initial root visit recognition U7 calculus count) stage) := A.actual_answer _ _ stage
theorem actual_born (stage : Nat) : type_of% (A.born_inventory (seed root visit recognition U7 calculus count)
    (frameAt root visit recognition U7 calculus count stage)) := A.born_inventory _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
