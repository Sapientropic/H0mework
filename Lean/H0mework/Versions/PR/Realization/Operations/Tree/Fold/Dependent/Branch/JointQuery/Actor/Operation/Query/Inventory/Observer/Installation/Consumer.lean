import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "Installation"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
namespace E.Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (presentation)
end E.Shared
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
 (actual_query actual_input completed_value paid_history actual_next actual_answer born_inventory)
end R
namespace Stock
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (updatedSeed supplied_seed_preserved)
end Stock
namespace F4
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace
 (dual_readback full_word complete_fibre cofinal_next recover_source action_source source_equation
  actual_operation actual_relation cochain_zero macro_payment no_refill noetherian rawSource)
end F4
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (stage : Nat)
def sourceFace : SourceNativeRootSemanticFaceAt (sourceRoot root visit recognition U7 calculus stage)
 (actualVisit root visit recognition U7 calculus stage) where
 projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (oldSourceRoot root visit recognition U7 calculus stage).source.base (component root visit recognition U7 calculus stage)).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
theorem source_material : (sourceFace root visit recognition U7 calculus stage).rootRead=
 sourceMaterial root visit recognition U7 calculus stage (actualOccurrence root visit recognition U7 calculus stage) := rfl
theorem installed_raw : installedReader root visit recognition U7 calculus stage
 (actualOccurrence root visit recognition U7 calculus stage)=Observer.raw root visit recognition U7 calculus stage := rfl
theorem complete_initial_value : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
 (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot
 (actualVisit root visit recognition U7 calculus stage).current (installedReader root visit recognition U7 calculus stage)=
 (Observer.raw root visit recognition U7 calculus stage).expression.eval (Observer.raw root visit recognition U7 calculus stage).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
theorem registered_paid : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
 (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot
 (actualVisit root visit recognition U7 calculus stage).current (installedReader root visit recognition U7 calculus stage)=
 (Observer.paid root visit recognition U7 calculus stage).2.2.1 := by
 rw [complete_initial_value]
 exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (E.Shared.base (actualFrame root visit recognition U7 calculus stage)).root.toAuthoritativeRoot
  (Observer.rawAt root visit recognition (actualFrame root visit recognition U7 calculus stage))
  (actualOccurrence root visit recognition U7 calculus stage)).symm
private theorem observation_from_paid {X : Type u} (value : X → Observer.Output root visit recognition)
 (x : X) (frame : Inventory.Action.Frame root visit recognition)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Inventory.Action.C.Occurrence frame (current:=current))
 (same : value x=(Observer.paidAt root visit recognition frame supplied).2.2.1)
 (index : Observer.Index root visit recognition) (kind : Fin 4) :
 (value x).2.1 index kind=Observer.observationValueAt root visit recognition frame supplied index kind :=
 (congrArg (fun output : Observer.Output root visit recognition => output.2.1 index kind) same).trans
 (Observer.paid_observation_at root visit recognition frame supplied index kind)
private theorem gram_from_paid {X : Type u} (value : X → Observer.Output root visit recognition)
 (x : X) (frame : Inventory.Action.Frame root visit recognition)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Inventory.Action.C.Occurrence frame (current:=current))
 (same : value x=(Observer.paidAt root visit recognition frame supplied).2.2.1)
 (first second : Observer.Sample root visit recognition) :
 ((value x).2.2 first second).down=
 inner ℂ (Observer.observationValueAt root visit recognition frame supplied first.1 first.2)
  (Observer.observationValueAt root visit recognition frame supplied second.1 second.2) :=
 (congrArg (fun output : Observer.Output root visit recognition => (output.2.2 first second).down) same).trans
 (Observer.paid_gram_at root visit recognition frame supplied first second)
theorem registered_observation (index : Observer.Index root visit recognition) (kind : Fin 4) :
 (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot
  (actualVisit root visit recognition U7 calculus stage).current
  (installedReader root visit recognition U7 calculus stage)).2.1 index kind=
 Observer.observationValueAt root visit recognition (actualFrame root visit recognition U7 calculus stage)
  (actualOccurrence root visit recognition U7 calculus stage) index kind := by
 exact observation_from_paid root visit recognition
  (fun _ : PUnit => RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
   (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot
   (actualVisit root visit recognition U7 calculus stage).current (installedReader root visit recognition U7 calculus stage))
  PUnit.unit (actualFrame root visit recognition U7 calculus stage)
  (actualOccurrence root visit recognition U7 calculus stage) (registered_paid root visit recognition U7 calculus stage) index kind
theorem registered_gram (first second : Observer.Sample root visit recognition) :
 ((RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot
  (actualVisit root visit recognition U7 calculus stage).current
  (installedReader root visit recognition U7 calculus stage)).2.2 first second).down=
 inner ℂ (Observer.observationValueAt root visit recognition (actualFrame root visit recognition U7 calculus stage)
  (actualOccurrence root visit recognition U7 calculus stage) first.1 first.2)
 (Observer.observationValueAt root visit recognition (actualFrame root visit recognition U7 calculus stage)
  (actualOccurrence root visit recognition U7 calculus stage) second.1 second.2) := by
 exact gram_from_paid root visit recognition
  (fun _ : PUnit => RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
   (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot
   (actualVisit root visit recognition U7 calculus stage).current (installedReader root visit recognition U7 calculus stage))
  PUnit.unit (actualFrame root visit recognition U7 calculus stage)
  (actualOccurrence root visit recognition U7 calculus stage) (registered_paid root visit recognition U7 calculus stage) first second
theorem exact_ledger : (sourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot.toLedgerRoot=
 (oldSourceRoot root visit recognition U7 calculus stage).toAuthoritativeRoot.toLedgerRoot := rfl
theorem exact_occurrence : (sourceRoot root visit recognition U7 calculus stage).emitted
 (actualVisit root visit recognition U7 calculus stage).current=actualOccurrence root visit recognition U7 calculus stage := rfl
theorem source_seed_preserved (event) (present : event ∈ (mappedSourceSeed root visit recognition U7 calculus).trace) :
 event ∈ (stock root visit recognition U7 calculus stage).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem scalar_preserved (event) (present : event ∈ (mappedScalar root visit recognition U7 calculus stage).trace) :
 event ∈ (stock root visit recognition U7 calculus stage).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem new_paid_preserved (event) (present : event ∈ (observerPaidStock root visit recognition U7 calculus stage).trace) :
 event ∈ (stock root visit recognition U7 calculus stage).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem registered_source : (initial root visit recognition U7 calculus stage).registered=
 (fixedFrame root visit recognition U7 calculus stage).registered := rfl
theorem actual_initial : (runtime root visit recognition U7 calculus stage).initialState.engine.node=
 .active (E.Shared.presentation (initial root visit recognition U7 calculus stage) (configuration root visit recognition U7 calculus stage)) := rfl
theorem initial_scalar : (initial root visit recognition U7 calculus stage).inventory=some (stock root visit recognition U7 calculus stage) := rfl
theorem initial_pair : (initial root visit recognition U7 calculus stage).pairInventory=some (mappedPair root visit recognition U7 calculus stage) := rfl
theorem stock_preserved (offset : Nat) (event) (present : event ∈ (stock root visit recognition U7 calculus stage).trace) :
 event ∈ (materialFace root visit recognition U7 calculus stage offset).rootRead.1.1.1.1.2.1.trace := by
 change event ∈ (Stock.updatedSeed (seed root visit recognition U7 calculus stage)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt root visit recognition U7 calculus stage offset))
  (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus stage offset))).trace
 have inSeed : event ∈ (seed root visit recognition U7 calculus stage).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
 exact Stock.supplied_seed_preserved (seed root visit recognition U7 calculus stage)
  (frameAt root visit recognition U7 calculus stage offset) event inSeed
theorem actual_disposition (offset : Nat) : (materialFace root visit recognition U7 calculus stage offset).rootRead.1.2.2.2.1=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.disposition
 (seed root visit recognition U7 calculus stage)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt root visit recognition U7 calculus stage offset))
 (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus stage offset)) := rfl
theorem actual_query (offset : Nat) : type_of% (R.actual_query (seed root visit recognition U7 calculus stage)
 (frameAt root visit recognition U7 calculus stage offset)) := R.actual_query _ _
theorem actual_input (offset : Nat) : type_of% (R.actual_input (seed root visit recognition U7 calculus stage)
 (initial root visit recognition U7 calculus stage) offset) := R.actual_input _ _ offset
theorem actual_result (offset : Nat) : type_of% (R.completed_value (seed root visit recognition U7 calculus stage)
 (frameAt root visit recognition U7 calculus stage offset)) := R.completed_value _ _
theorem actual_next (offset : Nat) : type_of% (R.actual_next (seed root visit recognition U7 calculus stage)
 (initial root visit recognition U7 calculus stage) offset) := R.actual_next _ _ offset
theorem born_whole : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first
 (initial root visit recognition U7 calculus stage) (configuration root visit recognition U7 calculus stage)) :=
 SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first _ _
theorem born_next : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next
 (initial root visit recognition U7 calculus stage) (configuration root visit recognition U7 calculus stage)) :=
 SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next _ _
theorem four_faces (offset : Nat) : type_of% (F4.dual_readback
 (seed root visit recognition U7 calculus stage) (initial root visit recognition U7 calculus stage) offset) :=
 F4.dual_readback _ _ offset
theorem complete_fibre (offset : Nat) (left right : SourceOperationScalarRelations.Formal ℤ
 (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (Observer.resultSlot root recognition)) :
 type_of% (F4.complete_fibre (seed root visit recognition U7 calculus stage)
 (initial root visit recognition U7 calculus stage) offset left right) := F4.complete_fibre _ _ offset left right
theorem cofinal_next (offset : Nat) (word : SourceOperationScalarRelations.Formal ℤ
 (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (Observer.resultSlot root recognition)) :
 type_of% (F4.cofinal_next (seed root visit recognition U7 calculus stage)
 (initial root visit recognition U7 calculus stage) offset word) := F4.cofinal_next _ _ offset word
theorem source_equation (offset : Nat) : type_of% (F4.source_equation
 (seed root visit recognition U7 calculus stage) (initial root visit recognition U7 calculus stage) offset) :=
 F4.source_equation _ _ offset
theorem inverse_whole (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
 (runtime root visit recognition U7 calculus stage) (F4.rawSource (seed root visit recognition U7 calculus stage)
 (initial root visit recognition U7 calculus stage)) ((runtime root visit recognition U7 calculus stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
 (runtime root visit recognition U7 calculus stage) (F4.rawSource (seed root visit recognition U7 calculus stage)
 (initial root visit recognition U7 calculus stage)) ((runtime root visit recognition U7 calculus stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
theorem macro_payment (offset : Nat) : type_of% (F4.macro_payment
 (seed root visit recognition U7 calculus stage) (initial root visit recognition U7 calculus stage) offset) :=
 F4.macro_payment _ _ offset
theorem no_refill (offset : Nat) : type_of% (F4.no_refill
 (seed root visit recognition U7 calculus stage) (initial root visit recognition U7 calculus stage) offset) :=
 F4.no_refill _ _ offset
theorem noetherian (offset : Nat) : type_of% (F4.noetherian
 (seed root visit recognition U7 calculus stage) (initial root visit recognition U7 calculus stage) offset) :=
 F4.noetherian _ _ offset
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
