import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Output
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
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

variable (letter : Letter root recognition visit successor) (historyWord : List (Letter root recognition visit successor))
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
abbrev pairExposure := SourceOperationPaidRelations.exposure
  (pairResult root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).2.1.2

theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord) := rfl
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.orbit))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (ledgerSeed root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)
      (frame root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairRaw root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)

theorem full_pair : (pairRaw root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).expression.eval
    (pairRaw root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).environment=
      (nextValue root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord,
        PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter (nextValue root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)-
          nextValue root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord) := by
  exact PaidSourceOrbit.NativeOrbitProgramme.pair_value (I:=Model root recognition visit successor transition alignment U7 calculus count)
    (O:=PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).integralFace.toAddMonoidHom
    (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom (current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord)
    (nextValue root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
