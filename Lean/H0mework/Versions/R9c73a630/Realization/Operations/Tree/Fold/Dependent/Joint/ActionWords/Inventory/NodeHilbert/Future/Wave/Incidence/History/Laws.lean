import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.History.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceMacroHistory"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroHistory
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
theorem lower_history (stage : Nat) : PaidSourceMacroLineage.lowerWord (historyWord.{u} stage)=
 SourceGeneratedLineageInventory.history stage := by
 change Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up _)=_
 rw [← Finsupp.mapDomain_comp]
 exact Finsupp.mapDomain_id

theorem raised_shift (word : SourceGeneratedLineageInventory.Word) :
 PaidSourceMacroLineage.raiseWord.{u} (SourceGeneratedLineageInventory.shift word)=
 PaidSourceMacroLineage.lineageShift (PaidSourceMacroLineage.raiseWord.{u} word) := by
 change Finsupp.mapDomain _ (Finsupp.mapDomain _ word)=Finsupp.mapDomain _ (Finsupp.mapDomain _ word)
 rw [← Finsupp.mapDomain_comp,← Finsupp.mapDomain_comp]
 rfl
theorem history_next (stage : Nat) : (programme.{u}).eval (environmentAt.{u} (historyWord.{u} stage))=historyWord.{u} (stage+1) := by
 change PaidSourceMacroLineage.actualWord.{u} 0+PaidSourceMacroLineage.lineageShift (historyWord.{u} stage)=
 PaidSourceMacroLineage.raiseWord.{u} (Finsupp.single 0 1+SourceGeneratedLineageInventory.shift (SourceGeneratedLineageInventory.history stage))
 rw [map_add,raised_shift]
 simp only [PaidSourceMacroLineage.raiseWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
theorem history_previous (stage : Nat) : (splitWord (historyWord.{u} (stage+1))).1=
 SourceGeneratedLineageInventory.history stage := by
 change SourceGeneratedLineageInventory.previous (PaidSourceMacroLineage.lowerWord (historyWord.{u} (stage+1)))=_
 rw [lower_history]
 exact SourceGeneratedLineageInventory.history_previous stage
theorem history_source (stage : Nat) : historyEmbedding root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter stage=
 ∑ index ∈ Finset.range (stage+1),SourceOperationInquiry.point (PaidSourceMacroLineage.nativeRuntime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
   ((PaidSourceMacroLineage.nativeRuntime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).stateAt index) :=
 (congrArg (PaidSourceMacroLineage.embed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) (lower_history stage)).trans
   (SourceGeneratedLineageInventory.history_source (PaidSourceMacroLineage.initial root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
     SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.chargedProgramme stage)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
