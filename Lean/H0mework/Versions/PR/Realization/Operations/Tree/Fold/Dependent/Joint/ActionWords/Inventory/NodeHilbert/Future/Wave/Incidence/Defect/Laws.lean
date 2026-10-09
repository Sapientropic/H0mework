import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Defect.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceHistoryDefect"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceHistoryDefect
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
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable (word : Word.{u})
theorem defect_read : type_of% (PaidRelationActionDefect.read_defect action.{u} (evaluation (R:=ℤ) (s:=Slot.orbit.{u}) (before root visit word)) (direction root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)) :=
 PaidRelationActionDefect.read_defect action.{u} (evaluation (R:=ℤ) (s:=Slot.orbit.{u}) (before root visit word)) (direction root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
theorem boundary_generated : boundary root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word=
 Finsupp.single PaidSourceMacroHistory.programme.{u} 1-
 Finsupp.single (.const (PaidSourceMacroHistory.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)) 1 :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_boundary (R:=ℤ)
 (paidRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) visit.current (actualReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
theorem source_environment : SourceSubstitution.sourceEnvironment binding.{u} (before root visit word)=
 PaidSourceMacroHistory.environmentAt.{u} (PaidSourceMacroHistory.nextValue root visit word) := by
 funext slot name
 cases slot <;> rfl
theorem value_from_source : type_of% (PaidRelationActionDefect.trace_action_value (before root visit word) binding.{u}
 (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace (paidRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) visit.current (actualReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))) :=
 PaidRelationActionDefect.trace_action_value (before root visit word) binding.{u}
 (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace (paidRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word) visit.current (actualReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))
theorem evaluated_difference : evaluated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word=
 PaidSourceMacroHistory.programme.{u}.eval (PaidSourceMacroHistory.environmentAt.{u} (PaidSourceMacroHistory.nextValue root visit word))-
 PaidSourceMacroHistory.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word :=
 (congrArg (fun relation => evaluation (R:=ℤ) (s:=Slot.orbit.{u}) (before root visit word) (action.{u} relation))
   (boundary_generated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).trans
   ((PaidRelationActionDefect.boundary_value (before root visit word) binding.{u} PaidSourceMacroHistory.programme.{u}
     (PaidSourceMacroHistory.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)).trans
       (congrArg (fun env => PaidSourceMacroHistory.programme.{u}.eval env-PaidSourceMacroHistory.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)
         (source_environment root visit word)))
theorem history_residual (stage : Nat) : evaluated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroHistory.historyWord.{u} stage)=
 PaidSourceMacroHistory.historyWord.{u} (stage+2)-PaidSourceMacroHistory.historyWord.{u} (stage+1) := by
 have next := (PaidSourceMacroHistory.normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroHistory.historyWord.{u} stage)).symm.trans
   (PaidSourceMacroHistory.history_output root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter stage)
 exact (evaluated_difference root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroHistory.historyWord.{u} stage)).trans
   (congrArg₂ (fun value result => PaidSourceMacroHistory.programme.{u}.eval (PaidSourceMacroHistory.environmentAt.{u} value)-result)
     next (PaidSourceMacroHistory.history_output root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter stage) |>.trans
       (congrArg (fun value => value-PaidSourceMacroHistory.historyWord.{u} (stage+1)) (PaidSourceMacroHistory.history_next.{u} (stage+1))))
theorem history_pulse (stage : Nat) : evaluated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (PaidSourceMacroHistory.historyWord.{u} stage)=
 PaidSourceMacroLineage.actualWord.{u} (stage+2) :=
 (history_residual root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter stage).trans (PaidRelationActionDefect.history_word_difference.{u} (stage+1))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceHistoryDefect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
