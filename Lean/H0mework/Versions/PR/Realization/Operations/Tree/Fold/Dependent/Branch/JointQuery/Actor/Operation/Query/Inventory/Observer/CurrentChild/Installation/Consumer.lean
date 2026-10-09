import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.Source
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
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation
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
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor stage : Nat)
def sourceFace : SourceNativeRootSemanticFaceAt (sourceRoot root visit recognition U7 calculus anchor stage)
 (actualVisit root visit recognition U7 calculus anchor stage) where
 projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (oldSourceRoot root visit recognition U7 calculus anchor stage).source.base (component root visit recognition U7 calculus anchor stage)).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
theorem source_material : (sourceFace root visit recognition U7 calculus anchor stage).rootRead=
 (materialAt root visit recognition U7 calculus anchor stage (actualOccurrence root visit recognition U7 calculus anchor stage),
 rawAt root visit recognition U7 calculus anchor stage (actualOccurrence root visit recognition U7 calculus anchor stage)) := rfl
theorem installed_raw : installedReader root visit recognition U7 calculus anchor stage
 (actualOccurrence root visit recognition U7 calculus anchor stage)=rawAt root visit recognition U7 calculus anchor stage (actualOccurrence root visit recognition U7 calculus anchor stage) := rfl
theorem complete_initial_value : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
 (sourceRoot root visit recognition U7 calculus anchor stage).toAuthoritativeRoot
 (actualVisit root visit recognition U7 calculus anchor stage).current (installedReader root visit recognition U7 calculus anchor stage)=
 (rawAt root visit recognition U7 calculus anchor stage (actualOccurrence root visit recognition U7 calculus anchor stage)).expression.eval (rawAt root visit recognition U7 calculus anchor stage (actualOccurrence root visit recognition U7 calculus anchor stage)).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
theorem registered_paid : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
 (sourceRoot root visit recognition U7 calculus anchor stage).toAuthoritativeRoot
 (actualVisit root visit recognition U7 calculus anchor stage).current (installedReader root visit recognition U7 calculus anchor stage)=
 (paidAt root visit recognition U7 calculus anchor stage (actualOccurrence root visit recognition U7 calculus anchor stage)).2.2.1 := by
 rw [complete_initial_value]
 exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (E.Shared.base (originalFrame root visit recognition U7 calculus anchor stage)).root.toAuthoritativeRoot
  (rawAt root visit recognition U7 calculus anchor stage)
  (actualOccurrence root visit recognition U7 calculus anchor stage)).symm
abbrev registeredValue := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
 (sourceRoot root visit recognition U7 calculus anchor stage).toAuthoritativeRoot
 (actualVisit root visit recognition U7 calculus anchor stage).current
 (installedReader root visit recognition U7 calculus anchor stage)
private theorem old_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition)
 (x : X) (same : value x=(paidAt root visit recognition U7 calculus anchor stage
  (actualOccurrence root visit recognition U7 calculus anchor stage)).2.2.1) :
 (value x).1=
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (CurrentChild.baseEnvironment root visit recognition U7 calculus anchor stage
   (actualOccurrence root visit recognition U7 calculus anchor stage)) +
 Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)).eval
   (Observer.Action.oldEnvironmentAt root visit recognition (originalFrame root visit recognition U7 calculus anchor stage)
    (actualOccurrence root visit recognition U7 calculus anchor stage))) :=
 (congrArg (fun output : CurrentChild.Output root visit recognition => output.1) same).trans
 (CurrentChild.paid_old_output root visit recognition U7 calculus anchor stage _)
theorem registered_old_output : (registeredValue root visit recognition U7 calculus anchor stage).1=
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (CurrentChild.baseEnvironment root visit recognition U7 calculus anchor stage
   (actualOccurrence root visit recognition U7 calculus anchor stage)) +
 Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)).eval
   (Observer.Action.oldEnvironmentAt root visit recognition (originalFrame root visit recognition U7 calculus anchor stage)
    (actualOccurrence root visit recognition U7 calculus anchor stage))) :=
 old_from_paid root visit recognition U7 calculus anchor stage
  (fun _ : PUnit => registeredValue root visit recognition U7 calculus anchor stage) PUnit.unit
  (registered_paid root visit recognition U7 calculus anchor stage)
private theorem actor_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition)
 (x : X) (same : value x=(paidAt root visit recognition U7 calculus anchor stage
  (actualOccurrence root visit recognition U7 calculus anchor stage)).2.2.1) :
 (value x).2.1.2 =
 (Finsupp.single (CurrentActor.actorAt root visit recognition U7 calculus anchor stage) 1,
  Finsupp.single (CurrentActor.nextActorAt root visit recognition U7 calculus anchor stage) 1 -
   Finsupp.single (CurrentActor.actorAt root visit recognition U7 calculus anchor stage) 1) :=
 (congrArg (fun output : CurrentChild.Output root visit recognition => output.2.1.2) same).trans
 (CurrentChild.paid_actor_pair root visit recognition U7 calculus anchor stage _)
private theorem observation_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition)
 (x : X) (same : value x=(paidAt root visit recognition U7 calculus anchor stage
  (actualOccurrence root visit recognition U7 calculus anchor stage)).2.2.1)
 (position : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length)
 (kind : Fin 4) :
 (value x).2.2.1 ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind=
 CurrentChild.observationValueAt root visit recognition U7 calculus anchor stage
  (actualOccurrence root visit recognition U7 calculus anchor stage)
  ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind :=
 (congrArg (fun output : CurrentChild.Output root visit recognition =>
  output.2.2.1 ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind) same).trans
 (CurrentChild.paid_observation_at root visit recognition U7 calculus anchor stage _ position kind)
private theorem gram_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition)
 (x : X) (same : value x=(paidAt root visit recognition U7 calculus anchor stage
  (actualOccurrence root visit recognition U7 calculus anchor stage)).2.2.1)
 (first second : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length × Fin 4) :
 ((value x).2.2.2
   (⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩,first.2)
   (⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩,second.2)).down =
 inner ℂ (CurrentChild.observationValueAt root visit recognition U7 calculus anchor stage
   (actualOccurrence root visit recognition U7 calculus anchor stage)
   ⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩ first.2)
  (CurrentChild.observationValueAt root visit recognition U7 calculus anchor stage
   (actualOccurrence root visit recognition U7 calculus anchor stage)
   ⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩ second.2) :=
 (congrArg (fun output : CurrentChild.Output root visit recognition =>
  (output.2.2.2 (⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩,first.2)
   (⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩,second.2)).down) same).trans
 (CurrentChild.paid_gram_at root visit recognition U7 calculus anchor stage _ first second)
theorem registered_actor : (registeredValue root visit recognition U7 calculus anchor stage).2.1.2 =
 (Finsupp.single (CurrentActor.actorAt root visit recognition U7 calculus anchor stage) 1,
  Finsupp.single (CurrentActor.nextActorAt root visit recognition U7 calculus anchor stage) 1 -
   Finsupp.single (CurrentActor.actorAt root visit recognition U7 calculus anchor stage) 1) :=
 actor_from_paid root visit recognition U7 calculus anchor stage
  (fun _ : PUnit => registeredValue root visit recognition U7 calculus anchor stage) PUnit.unit
  (registered_paid root visit recognition U7 calculus anchor stage)
theorem registered_observation
 (position : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length)
 (kind : Fin 4) :
 (registeredValue root visit recognition U7 calculus anchor stage).2.2.1
  ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind=
 CurrentChild.observationValueAt root visit recognition U7 calculus anchor stage
  (actualOccurrence root visit recognition U7 calculus anchor stage)
  ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind :=
 observation_from_paid root visit recognition U7 calculus anchor stage
  (fun _ : PUnit => registeredValue root visit recognition U7 calculus anchor stage) PUnit.unit
  (registered_paid root visit recognition U7 calculus anchor stage) position kind
theorem registered_gram
 (first second : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length × Fin 4) :
 ((registeredValue root visit recognition U7 calculus anchor stage).2.2.2
   (⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩,first.2)
   (⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩,second.2)).down =
 inner ℂ (CurrentChild.observationValueAt root visit recognition U7 calculus anchor stage
   (actualOccurrence root visit recognition U7 calculus anchor stage)
   ⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩ first.2)
  (CurrentChild.observationValueAt root visit recognition U7 calculus anchor stage
   (actualOccurrence root visit recognition U7 calculus anchor stage)
   ⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩ second.2) :=
 gram_from_paid root visit recognition U7 calculus anchor stage
  (fun _ : PUnit => registeredValue root visit recognition U7 calculus anchor stage) PUnit.unit
  (registered_paid root visit recognition U7 calculus anchor stage) first second
theorem exact_ledger : (sourceRoot root visit recognition U7 calculus anchor stage).toAuthoritativeRoot.toLedgerRoot=
 (oldSourceRoot root visit recognition U7 calculus anchor stage).toAuthoritativeRoot.toLedgerRoot := rfl
theorem exact_occurrence : (sourceRoot root visit recognition U7 calculus anchor stage).emitted
 (actualVisit root visit recognition U7 calculus anchor stage).current=actualOccurrence root visit recognition U7 calculus anchor stage := rfl
theorem source_seed_preserved (event) (present : event ∈ (mappedSeed root visit recognition U7 calculus anchor).trace) :
 event ∈ (stock root visit recognition U7 calculus anchor stage).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem scalar_preserved (event) (present : event ∈ (mappedScalar root visit recognition U7 calculus anchor stage).trace) :
 event ∈ (stock root visit recognition U7 calculus anchor stage).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem new_paid_preserved (event) (present : event ∈ (paidStock root visit recognition U7 calculus anchor stage).trace) :
 event ∈ (stock root visit recognition U7 calculus anchor stage).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem registered_source : (initial root visit recognition U7 calculus anchor stage).registered=
 (fixedFrame root visit recognition U7 calculus anchor stage).registered := rfl
theorem actual_initial : (runtime root visit recognition U7 calculus anchor stage).initialState.engine.node=
 .active (E.Shared.presentation (initial root visit recognition U7 calculus anchor stage) (configuration root visit recognition U7 calculus anchor stage)) := rfl
theorem initial_scalar : (initial root visit recognition U7 calculus anchor stage).inventory=some (stock root visit recognition U7 calculus anchor stage) := rfl
theorem initial_pair : (initial root visit recognition U7 calculus anchor stage).pairInventory=some (mappedPair root visit recognition U7 calculus anchor stage) := rfl
theorem stock_preserved (offset : Nat) (event) (present : event ∈ (stock root visit recognition U7 calculus anchor stage).trace) :
 event ∈ (materialFace root visit recognition U7 calculus anchor stage offset).rootRead.1.1.1.1.2.1.trace := by
 change event ∈ (Stock.updatedSeed (seed root visit recognition U7 calculus anchor stage)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt root visit recognition U7 calculus anchor stage offset))
  (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor stage offset))).trace
 have inSeed : event ∈ (seed root visit recognition U7 calculus anchor stage).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
 exact Stock.supplied_seed_preserved (seed root visit recognition U7 calculus anchor stage)
  (frameAt root visit recognition U7 calculus anchor stage offset) event inSeed
theorem actual_disposition (offset : Nat) : (materialFace root visit recognition U7 calculus anchor stage offset).rootRead.1.2.2.2.1=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.disposition
 (seed root visit recognition U7 calculus anchor stage)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frameAt root visit recognition U7 calculus anchor stage offset))
 (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor stage offset)) := rfl
theorem actual_query (offset : Nat) : type_of% (R.actual_query (seed root visit recognition U7 calculus anchor stage)
 (frameAt root visit recognition U7 calculus anchor stage offset)) := R.actual_query _ _
theorem actual_input (offset : Nat) : type_of% (R.actual_input (seed root visit recognition U7 calculus anchor stage)
 (initial root visit recognition U7 calculus anchor stage) offset) := R.actual_input _ _ offset
theorem actual_result (offset : Nat) : type_of% (R.completed_value (seed root visit recognition U7 calculus anchor stage)
 (frameAt root visit recognition U7 calculus anchor stage offset)) := R.completed_value _ _
theorem actual_next (offset : Nat) : type_of% (R.actual_next (seed root visit recognition U7 calculus anchor stage)
 (initial root visit recognition U7 calculus anchor stage) offset) := R.actual_next _ _ offset
theorem born_whole : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first
 (initial root visit recognition U7 calculus anchor stage) (configuration root visit recognition U7 calculus anchor stage)) :=
 SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first _ _
theorem born_next : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next
 (initial root visit recognition U7 calculus anchor stage) (configuration root visit recognition U7 calculus anchor stage)) :=
 SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next _ _
theorem four_faces (offset : Nat) : type_of% (F4.dual_readback
 (seed root visit recognition U7 calculus anchor stage) (initial root visit recognition U7 calculus anchor stage) offset) :=
 F4.dual_readback _ _ offset
theorem complete_fibre (offset : Nat) (left right : SourceOperationScalarRelations.Formal ℤ
 (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition)) :
 type_of% (F4.complete_fibre (seed root visit recognition U7 calculus anchor stage)
 (initial root visit recognition U7 calculus anchor stage) offset left right) := F4.complete_fibre _ _ offset left right
theorem cofinal_next (offset : Nat) (word : SourceOperationScalarRelations.Formal ℤ
 (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition)) :
 type_of% (F4.cofinal_next (seed root visit recognition U7 calculus anchor stage)
 (initial root visit recognition U7 calculus anchor stage) offset word) := F4.cofinal_next _ _ offset word
theorem source_equation (offset : Nat) : type_of% (F4.source_equation
 (seed root visit recognition U7 calculus anchor stage) (initial root visit recognition U7 calculus anchor stage) offset) :=
 F4.source_equation _ _ offset
theorem inverse_whole (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
 (runtime root visit recognition U7 calculus anchor stage) (F4.rawSource (seed root visit recognition U7 calculus anchor stage)
 (initial root visit recognition U7 calculus anchor stage)) ((runtime root visit recognition U7 calculus anchor stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
 (runtime root visit recognition U7 calculus anchor stage) (F4.rawSource (seed root visit recognition U7 calculus anchor stage)
 (initial root visit recognition U7 calculus anchor stage)) ((runtime root visit recognition U7 calculus anchor stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
theorem macro_payment (offset : Nat) : type_of% (F4.macro_payment
 (seed root visit recognition U7 calculus anchor stage) (initial root visit recognition U7 calculus anchor stage) offset) :=
 F4.macro_payment _ _ offset
theorem no_refill (offset : Nat) : type_of% (F4.no_refill
 (seed root visit recognition U7 calculus anchor stage) (initial root visit recognition U7 calculus anchor stage) offset) :=
 F4.no_refill _ _ offset
theorem noetherian (offset : Nat) : type_of% (F4.noetherian
 (seed root visit recognition U7 calculus anchor stage) (initial root visit recognition U7 calculus anchor stage) offset) :=
 F4.noetherian _ _ offset
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
