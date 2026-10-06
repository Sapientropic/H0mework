import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Response.Installation
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceMacroResponse"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroResponse
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)


variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
variable (word : Word.{u})
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
 (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).toAuthoritativeRoot visit.current (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word=projection root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroLineage.lineageShift word) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
theorem normal_action : normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word=advance root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (projection root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) :=
 (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).trans
   (SourceGeneratedActionWords.advance_source actions (observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) PUnit.unit PUnit.unit word).symm
theorem source_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
 (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).toAuthoritativeRoot visit.current (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).length=3 :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _
def nextFibre := follow root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (projection root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (retained root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).2
theorem fibre_actual : (nextFibre root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).val=PaidSourceMacroLineage.lineageShift word := rfl
theorem complete_action : type_of% (SourceGeneratedActionWords.complete_advance_source actions
  (observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) PUnit.unit PUnit.unit word) :=
 SourceGeneratedActionWords.complete_advance_source actions (observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) PUnit.unit PUnit.unit word
theorem complete_read (following : List PUnit.{u+1}) : type_of% (SourceGeneratedActionWords.complete_read_source actions
  (observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) PUnit.unit following word) :=
 SourceGeneratedActionWords.complete_read_source actions (observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) PUnit.unit following word
namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
 (queryAt nextAt no_refill noetherian old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) ∧
 type_of% (Request.nextAt (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) := ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) ∧
 type_of% (Request.noetherian (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) := ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem all_inventory : type_of% (Request.old_past_born (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)) := Request.old_past_born _ _
abbrev sourceExposure := SourceOperationPaidRelations.exposure (result root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).2.1.2
abbrev pairExposure := SourceOperationPaidRelations.exposure (pairResult root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).2.1.2
theorem source_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).inventory=some (sourceExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) := rfl
theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).pairInventory=some (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) := rfl
theorem source_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) Var.{u} Slot.orbit))
 (present : event ∈ (sourceExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).trace) :
 event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.updatedSeed (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))).trace := by
 exact PaidSourceOrbit.SourceInventoryReceipt.consumed (Values:=Value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) (Variables:=Var.{u}) (sort:=Slot.orbit)
  (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (sourceExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (source_inventory root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) event present
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
 (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)) Var.{u} Slot.orbit))
 (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).trace) :
 event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
 (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
abbrev actualGenerated (stage : Nat) := (generated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroLineage.actualWord.{u} stage),
  nextFibre root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroLineage.actualWord.{u} stage))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
