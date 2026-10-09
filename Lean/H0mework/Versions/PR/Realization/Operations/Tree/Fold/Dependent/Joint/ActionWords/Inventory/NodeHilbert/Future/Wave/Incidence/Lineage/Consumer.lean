import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Lineage.Installation
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceMacroLineage"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroLineage
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
variable (word : LineageWord.{u})
theorem seed_value : current root visit word=word :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).toAuthoritativeRoot visit.current (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word=nextValue root visit word :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
theorem source_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
  (seedReader root word)).length=1 := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _
theorem action_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).toAuthoritativeRoot visit.current (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).length=2 :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _
theorem lower_shift : lowerWord (lineageShift word)=Native.shift (lowerWord word) := by
 change Finsupp.mapDomain _ (Finsupp.mapDomain _ word)=Finsupp.mapDomain _ (Finsupp.mapDomain _ word)
 rw [← Finsupp.mapDomain_comp,← Finsupp.mapDomain_comp]
 rfl
theorem source_normal : lowerWord (normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)=Native.shift (lowerWord word) :=
 (congrArg lowerWord (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).trans
   ((congrArg (fun value => lowerWord (lineageShift value)) (seed_value root visit word)).trans (lower_shift word))
theorem actual_source_action : embed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord (normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))=
    SourceOperationInquiry.sourceAction (nativeRuntime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) (embed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord word)) :=
 (congrArg (embed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) (source_normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).trans
   (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage.after_source
     (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.chargedProgramme (lowerWord word))
theorem physical_effect : observed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord (normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))-observed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord word)=
    effect root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord word) :=
 (congrArg (fun value => observed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter value-observed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord word))
   (source_normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).trans
     (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage.after_observed
       (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.chargedProgramme (lowerWord word))
namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) ∧
    type_of% (Request.nextAt (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) :=
 ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) ∧
    type_of% (Request.noetherian (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) stage) :=
 ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem all_inventory : type_of% (Request.old_past_born (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)) :=
 Request.old_past_born _ _
abbrev seedExposure := SourceOperationPaidRelations.exposure (seedResult root visit word).2.1.2
abbrev pairExposure := SourceOperationPaidRelations.exposure (pairResult root visit word).2.1.2
theorem source_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).inventory=some (seedExposure root visit word) := rfl
theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word).pairInventory=some (pairExposure root visit word) := rfl
theorem source_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr Value.{u} Var.{u} Slot.orbit))
    (present : event ∈ (seedExposure root visit word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.updatedSeed
      (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))).trace := by
 exact PaidSourceOrbit.SourceInventoryReceipt.consumed
    (Values:=Value.{u}) (Variables:=Var.{u}) (sort:=Slot.orbit)
    (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (seedExposure root visit word)
    (source_inventory root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) event present
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue Value.{u}) Var.{u} Slot.orbit))
    (present : event ∈ (pairExposure root visit word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem actual_word_source (stage : Nat) : embed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (lowerWord (actualWord stage))=
    SourceOperationInquiry.point (nativeRuntime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) ((nativeRuntime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).stateAt stage) := by
 simp only [lowerWord,actualWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
 exact SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage.embed_point
   (initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
   SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.chargedProgramme stage
theorem actual_word_next (stage : Nat) : normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (actualWord stage)=actualWord (stage+1) :=
 (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (actualWord stage)).trans
   ((congrArg lineageShift (seed_value root visit (actualWord stage))).trans
     (by simp only [lineageShift,actualWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]))
abbrev actualGenerated (stage : Nat) := (generated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (actualWord stage),
  PaidSourceNextInventory.fieldGenerated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroLineage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
