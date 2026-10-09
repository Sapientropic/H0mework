import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory.Programme
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
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

variable (point : I.Carrier root recognition visit successor)
variable (word : List (I.Letter root recognition visit successor))
abbrev singleResult (letter : I.Letter root recognition visit successor) (sourcePoint : I.Carrier root recognition visit successor) :=
  paidSourceResult root recognition visit successor transition alignment U7 calculus count sourcePoint [letter]
def historyInventory : List (I.Letter root recognition visit successor) → I.Carrier root recognition visit successor →
    RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (Value root recognition visit successor) Var Slot.waves))
  | [],sourcePoint => SourceOperationPaidRelations.exposure
      (paidSourceResult root recognition visit successor transition alignment U7 calculus count sourcePoint []).2.1.2
  | letter::rest,sourcePoint => SourceHistoryCommon.seed
      (SourceOperationPaidRelations.exposure
        (singleResult root recognition visit successor transition alignment U7 calculus count letter sourcePoint).2.1.2)
      (historyInventory rest (I.actions root recognition visit successor transition alignment U7 calculus count letter sourcePoint))
def historyCost : List (I.Letter root recognition visit successor) → I.Carrier root recognition visit successor → Nat
  | [],sourcePoint => (paidSourceResult root recognition visit successor transition alignment U7 calculus count sourcePoint []).2.1.2.length
  | letter::rest,sourcePoint => (singleResult root recognition visit successor transition alignment U7 calculus count letter sourcePoint).2.1.2.length+
      historyCost rest (I.actions root recognition visit successor transition alignment U7 calculus count letter sourcePoint)
theorem source_result_cost (sourcePoint : I.Carrier root recognition visit successor)
    (letters : List (I.Letter root recognition visit successor)) :
    (paidSourceResult root recognition visit successor transition alignment U7 calculus count sourcePoint letters).2.1.2.length=2*letters.length+5 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count letters)
theorem history_cost : historyCost root recognition visit successor transition alignment U7 calculus count word point=7*word.length+5 := by
  induction word generalizing point with
  | nil => exact source_result_cost root recognition visit successor transition alignment U7 calculus count point []
  | cons letter rest previous =>
    rw [historyCost,source_result_cost,previous]
    simp only [List.length_cons,List.length_nil]
    omega
abbrev completeInventory := SourceHistoryCommon.seed
  (SourceOperationPaidRelations.exposure (paidSourceResult root recognition visit successor transition alignment U7 calculus count point word).2.1.2)
  (historyInventory root recognition visit successor transition alignment U7 calculus count word point)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
