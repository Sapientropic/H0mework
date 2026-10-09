import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment
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
variable (sourceFrame : Frame.{u})
theorem source_value : (Shared.resultFace sourceFrame configuration).rootRead.2.2.1=
    (sourceRaw (A.epoch sourceFrame)).expression.eval (sourceRaw (A.epoch sourceFrame)).environment :=
 O.source_value (Shared.baseRoot sourceFrame configuration).toAuthoritativeRoot
  (Shared.datum sourceFrame configuration).reader (Shared.actualOccurrence sourceFrame)
theorem paid_environment : (Shared.resultFace sourceFrame configuration).rootRead.2.2.1.1+
    (Shared.resultFace sourceFrame configuration).rootRead.2.2.1.2=
 PaidSourceMacroHistory.programme.{u}.eval (A.epoch sourceFrame).activeEnvironment := by
 rw [source_value]
 unfold sourceRaw
 rw [SourceOperationScalarInventoryLift.eval_liftExpr]
 have updated := SourceOperationEffects.Expr.eval_update PaidSourceMacroHistory.programme.{u}
  (A.epoch sourceFrame).rawRead.environment ((A.epoch sourceFrame).activeEnvironment-(A.epoch sourceFrame).rawRead.environment)
 rw [add_sub_cancel] at updated
 exact updated.symm
theorem born_environment {current : (Shared.nextBorn sourceFrame configuration).V.Current}
 (occurrence : (Shared.nextBorn sourceFrame configuration).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
 (Shared.nextBorn sourceFrame configuration).environment occurrence=
 PaidSourceMacroHistory.environmentAt.{u} (PaidSourceMacroHistory.programme.{u}.eval (A.epoch sourceFrame).activeEnvironment) :=
 congrArg PaidSourceMacroHistory.environmentAt.{u} (paid_environment sourceFrame)
theorem born_active : (A.epoch (Shared.nextBorn sourceFrame configuration)).activeEnvironment Slot.orbit PUnit.unit=
 PaidSourceMacroHistory.programme.{u}.eval (A.epoch sourceFrame).activeEnvironment :=
 congrArg (fun env : Env Value Var => env Slot.orbit PUnit.unit) (born_environment sourceFrame _)
theorem twice_active : (A.epoch (Shared.nextBorn (Shared.nextBorn sourceFrame configuration) configuration)).activeEnvironment Slot.orbit PUnit.unit=
 PaidSourceMacroHistory.programme.{u}.eval
   (PaidSourceMacroHistory.environmentAt.{u} (PaidSourceMacroHistory.programme.{u}.eval (A.epoch sourceFrame).activeEnvironment)) :=
 (born_active (Shared.nextBorn sourceFrame configuration)).trans
   (congrArg PaidSourceMacroHistory.programme.{u}.eval (born_environment sourceFrame _))
theorem born_source_inventory : (Shared.nextBorn sourceFrame configuration).inventory=nextInventory sourceFrame := rfl
theorem born_pair_inventory : (Shared.nextBorn sourceFrame configuration).pairInventory=nextPairInventory sourceFrame := rfl
theorem source_inventory_old (prior : RootedAccountedUnfolding
 (CofinalHistorySettlement.PresentedRelationEventAt (Expr Value.{u} Var.{u} Slot.orbit)))
 (actual : sourceFrame.inventory=some prior) :
 SourceHistoryCommon.Exposure prior ((Shared.nextBorn sourceFrame configuration).inventory.getD prior) := by
 change SourceHistoryCommon.Exposure prior ((nextInventory sourceFrame).getD prior)
 unfold nextInventory
 rw [actual]
 exact SourceHistoryCommon.parallel_left _ _ _
theorem source_inventory_paid : SourceHistoryCommon.Exposure
 (SourceOperationPaidRelations.exposure sourceFrame.paidRead.state.2)
 ((Shared.nextBorn sourceFrame configuration).inventory.getD
   (SourceOperationPaidRelations.exposure sourceFrame.paidRead.state.2)) := by
 change SourceHistoryCommon.Exposure _ ((nextInventory sourceFrame).getD _)
 unfold nextInventory
 cases sourceFrame.inventory with
 | none => exact ⟨fun _ present => present,fun _ present => present⟩
 | some prior => exact SourceHistoryCommon.parallel_right _ _ _
theorem pair_inventory_old (prior : RootedAccountedUnfolding
 (CofinalHistorySettlement.PresentedRelationEventAt
  (Expr (SourceOperationScalarInventoryLift.PairValue Value.{u}) Var.{u} Slot.orbit)))
 (actual : sourceFrame.pairInventory=some prior) :
 SourceHistoryCommon.Exposure prior ((Shared.nextBorn sourceFrame configuration).pairInventory.getD prior) := by
 change SourceHistoryCommon.Exposure prior ((nextPairInventory sourceFrame).getD prior)
 unfold nextPairInventory
 rw [actual]
 exact SourceHistoryCommon.parallel_left _ _ _
theorem pair_inventory_paid : SourceHistoryCommon.Exposure
 (SourceOperationPaidRelations.exposure (sourceResult sourceFrame).2.1.2)
 ((Shared.nextBorn sourceFrame configuration).pairInventory.getD
   (SourceOperationPaidRelations.exposure (sourceResult sourceFrame).2.1.2)) := by
 change SourceHistoryCommon.Exposure _ ((nextPairInventory sourceFrame).getD _)
 unfold nextPairInventory
 cases sourceFrame.pairInventory with
 | none => exact ⟨fun _ present => present,fun _ present => present⟩
 | some prior => exact SourceHistoryCommon.parallel_right _ _ _
theorem source_result_trace : HEq (sourceResult sourceFrame).2.1.2
    (Shared.resultFace sourceFrame configuration).rootRead.2.1.2 := HEq.rfl
variable (word : PaidSourceMacroHistory.Word.{u})
abbrev initial := PaidSourceMacroHistory.frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word
abbrev runtime := Shared.runtime (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration
theorem initial_environment :
 (A.epoch (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).activeEnvironment=
 PaidSourceMacroHistory.environmentAt.{u} (PaidSourceMacroHistory.nextValue root visit word) := rfl
theorem history_born (stage : Nat) :
 (A.epoch (Shared.nextBorn (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter
  (PaidSourceMacroHistory.historyWord.{u} stage)) configuration)).activeEnvironment Slot.orbit PUnit.unit=
 PaidSourceMacroHistory.historyWord.{u} (stage+2) := by
 rw [born_active,initial_environment]
 have first : PaidSourceMacroHistory.nextValue root visit (PaidSourceMacroHistory.historyWord.{u} stage)=
   PaidSourceMacroHistory.historyWord.{u} (stage+1) :=
  (congrArg (fun value => PaidSourceMacroHistory.programme.{u}.eval (PaidSourceMacroHistory.environmentAt.{u} value))
   (PaidSourceMacroHistory.seed_value root visit (PaidSourceMacroHistory.historyWord.{u} stage))).trans
   (PaidSourceMacroHistory.history_next stage)
 rw [first]
 exact PaidSourceMacroHistory.history_next (stage+1)
theorem canonical_query (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query
  (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query _ configuration stage
theorem canonical_answer (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer
  (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer _ configuration stage
theorem canonical_next (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next
  (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next _ configuration stage
theorem same_debt (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill configuration
  (Shared.frames (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration stage)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill configuration _
theorem noetherian (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded configuration
  (Shared.frames (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration stage)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded configuration _
theorem current_whole (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current configuration
  (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current configuration _ stage
abbrev actualGenerated := (runtime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word,
 fun stage => Shared.resultFace (Shared.frames (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) configuration stage) configuration,
 PaidSourceMacroHistory.generated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
