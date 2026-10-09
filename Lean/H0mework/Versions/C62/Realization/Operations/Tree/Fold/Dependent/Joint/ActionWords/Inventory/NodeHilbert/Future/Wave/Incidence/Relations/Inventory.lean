import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Relations.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceRelations
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


variable (letter : Letter root recognition visit successor)
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor))
variable (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
variable (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot)
abbrev sourceExposure := SourceOperationPaidRelations.exposure (sourceResult root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression).2.1.2
abbrev pairExposure := SourceOperationPaidRelations.exposure (pairResult root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression).2.1.2
theorem source_inventory : (frame root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression).inventory=some (sourceExposure root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression) := rfl
theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression).pairInventory=some (pairExposure root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression) := rfl
theorem source_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot))
    (present : event ∈ (sourceExposure root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.updatedSeed
      (ledgerSeed root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression) (frame root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression))).trace :=
  PaidSourceOrbit.SourceInventoryReceipt.consumed _ _ _ (source_inventory root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression) event present
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
    (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var slot))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (ledgerSeed root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression) (frame root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (frame root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
