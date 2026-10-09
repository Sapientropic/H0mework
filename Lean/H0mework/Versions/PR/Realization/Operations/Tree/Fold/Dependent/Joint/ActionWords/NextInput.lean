import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
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
variable (point : Carrier root recognition visit successor) (word : List Letter)
def actedFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Joint.actualRoot root visit recognition successor transition alignment).source.base
    (component root recognition visit successor transition alignment U7 calculus count point word)).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

theorem same_execution : HEq
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
      (reader root recognition visit successor transition alignment U7 calculus count point word))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (original root recognition visit successor transition alignment) visit.current
      (originalReader root recognition visit successor transition alignment U7 calculus count point word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (sourceRaw root recognition visit successor transition alignment U7 calculus count point word)

theorem acted_read : (actedFace root recognition visit successor transition alignment U7 calculus count point word).rootRead =
    acted root recognition visit successor transition alignment U7 calculus count point word := rfl

theorem input_point : (actedFace root recognition visit successor transition alignment U7 calculus count point word).rootRead.1 =
    SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point :=
  acted_value root recognition visit successor transition alignment U7 calculus count point word

theorem actual_environment {current : (frame root recognition visit successor transition alignment U7 calculus count point word).V.Current}
    (occurrence : (frame root recognition visit successor transition alignment U7 calculus count point word).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (frame root recognition visit successor transition alignment U7 calculus count point word).environment occurrence =
      environment root recognition visit successor transition alignment U7 calculus count
        (actions root recognition visit successor transition alignment U7 calculus count Letter.simultaneous.{u}
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point)) :=
  congrArg (fun value => environment root recognition visit successor transition alignment U7 calculus count
    (actions root recognition visit successor transition alignment U7 calculus count Letter.simultaneous.{u} value))
      (acted_value root recognition visit successor transition alignment U7 calculus count point word)

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem next_query (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  Request.queryAt _ _ stage

theorem next_whole (stage : Nat) : type_of% (Request.nextAt
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  Request.nextAt _ _ stage

theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point word)
      (frame root recognition visit successor transition alignment U7 calculus count point word) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩

theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word)) :=
  Request.installed_born_inventory _ _

theorem old_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count point word)
    (frame root recognition visit successor transition alignment U7 calculus count point word)) :=
  Request.old_past_born _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
