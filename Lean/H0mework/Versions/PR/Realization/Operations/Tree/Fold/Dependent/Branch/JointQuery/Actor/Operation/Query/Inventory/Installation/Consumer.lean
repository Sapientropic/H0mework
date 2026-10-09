import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.Consumer

import Lean.LibrarySuggestions.Basic
-- These complete runtime mouths are consumed directly, without suggestion search.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "Installation"

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
  (actual_query actual_input completed_value paid_history actual_next actual_answer born_inventory)
end A
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence root visit)
end Shared
end E
namespace Stock
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (updatedSeed supplied_seed_preserved)
end Stock
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)

def sourceFace : SourceNativeRootSemanticFaceAt (sourceRoot root visit recognition) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Actor.Installation.sourceRoot root visit recognition).source.base (component root visit recognition)).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
theorem installed_raw : installedReader root visit recognition (root.emitted visit.current)=Inventory.raw root visit recognition := rfl
theorem complete_initial_value : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
    (sourceRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition)=
    (Inventory.raw root visit recognition).expression.eval (Inventory.raw root visit recognition).environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
theorem source_material : (sourceFace root visit recognition).rootRead=sourceMaterial root visit recognition := rfl
theorem exact_ledger : (sourceRoot root visit recognition).toAuthoritativeRoot.toLedgerRoot=root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem exact_occurrence : (sourceRoot root visit recognition).emitted visit.current=root.emitted visit.current := rfl
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem registered_source : (initial root visit recognition U7 calculus).registered=
    (fixedFrame root visit recognition U7 calculus).registered := rfl
theorem initial_inventory : (initial root visit recognition U7 calculus).inventory=some (Inventory.stock root visit recognition) := rfl
theorem actual_initial : (runtime root visit recognition U7 calculus).initialState.engine.node=
    .active (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
      (initial root visit recognition U7 calculus) (configuration root visit recognition U7 calculus)) := rfl
theorem stock_preserved (stage : Nat) (event) (present : event ∈ (Inventory.stock root visit recognition).trace) :
    event ∈ (materialFace root visit recognition U7 calculus stage).rootRead.1.1.1.1.2.1.trace := by
  change event ∈ (Stock.updatedSeed (seed root visit recognition U7 calculus)
    (E.epoch (frameAt root visit recognition U7 calculus stage))
    (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus stage))).trace
  have inSeed : event ∈ (seed root visit recognition U7 calculus).trace :=
    (SourceHistoryCommon.parallel_left _ _ _).1 event present
  exact Stock.supplied_seed_preserved (seed root visit recognition U7 calculus)
    (frameAt root visit recognition U7 calculus stage) event inSeed
theorem actual_disposition (stage : Nat) : (materialFace root visit recognition U7 calculus stage).rootRead.1.2.2.2.1=
    SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.disposition
      (seed root visit recognition U7 calculus) (E.epoch (frameAt root visit recognition U7 calculus stage))
      (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus stage)) := rfl
theorem actual_query (stage : Nat) : type_of% (A.actual_query (seed root visit recognition U7 calculus)
    (frameAt root visit recognition U7 calculus stage)) := A.actual_query _ _
theorem actual_input (stage : Nat) : type_of% (A.actual_input (seed root visit recognition U7 calculus)
    (initial root visit recognition U7 calculus) stage) := A.actual_input _ _ stage
theorem actual_result (stage : Nat) : type_of% (A.completed_value (seed root visit recognition U7 calculus)
    (frameAt root visit recognition U7 calculus stage)) := A.completed_value _ _
theorem paid_trace (stage : Nat) : type_of% (A.paid_history (seed root visit recognition U7 calculus)
    (frameAt root visit recognition U7 calculus stage)) := A.paid_history _ _
theorem actual_next (stage : Nat) : type_of% (A.actual_next (seed root visit recognition U7 calculus)
    (initial root visit recognition U7 calculus) stage) := A.actual_next _ _ stage
theorem actual_answer (stage : Nat) : type_of% (A.actual_answer (seed root visit recognition U7 calculus)
    (initial root visit recognition U7 calculus) stage) := A.actual_answer _ _ stage
theorem actual_born (stage : Nat) : type_of% (A.born_inventory (seed root visit recognition U7 calculus)
    (frameAt root visit recognition U7 calculus stage)) := A.born_inventory _ _

theorem born_disposition : type_of%
    (SourceGeneratedInquiryReceiptAction.Inventory.Born.actual_disposition
      (initial root visit recognition U7 calculus) (configuration root visit recognition U7 calculus)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.actual_disposition _ _
theorem born_query : type_of%
    (SourceGeneratedInquiryReceiptAction.Inventory.Born.actual_query
      (initial root visit recognition U7 calculus) (configuration root visit recognition U7 calculus)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.actual_query _ _
theorem born_whole : type_of%
    (SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first
      (initial root visit recognition U7 calculus) (configuration root visit recognition U7 calculus)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first _ _
theorem born_next : type_of%
    (SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next
      (initial root visit recognition U7 calculus) (configuration root visit recognition U7 calculus)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next _ _
theorem source_equation (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.source_equation
      (seed root visit recognition U7 calculus) (initial root visit recognition U7 calculus) stage) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.source_equation _ _ stage
theorem complete_query_trace (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.complete_query_trace
      (seed root visit recognition U7 calculus) (initial root visit recognition U7 calculus) stage) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.complete_query_trace _ _ stage
theorem four_face_dual (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.dual_readback
      (seed root visit recognition U7 calculus) (initial root visit recognition U7 calculus) stage) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.dual_readback _ _ stage

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
