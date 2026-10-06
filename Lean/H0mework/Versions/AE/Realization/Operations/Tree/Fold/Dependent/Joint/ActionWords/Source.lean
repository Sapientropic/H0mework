import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Action
import H0mework.Realization.ObservationActions.WordsModel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
namespace J
export SourceOperationNative.Tree.Fold.Dependent.Joint (actionPacket normedAction normedObservation)
end J
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
abbrev Carrier := SourceHistoryCommon.Root.Action.Joint root visit recognition successor
inductive Letter : Type u | source | target | simultaneous
def actions : Letter → Carrier root recognition visit successor →ₗ[ℤ] Carrier root recognition visit successor
 | .source => (J.actionPacket root visit recognition successor transition alignment U7 calculus count).source.sourceAction.carrierAction.prodMap LinearMap.id
 | .target => LinearMap.id.prodMap (J.actionPacket root visit recognition successor transition alignment U7 calculus count).target.sourceAction.carrierAction
 | .simultaneous => J.normedAction root visit recognition successor transition alignment U7 calculus count
abbrev read := J.normedObservation root visit recognition successor transition alignment U7 calculus count
abbrev Model := SourceGeneratedActionWords.Model (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) .simultaneous
abbrev projection := SourceGeneratedActionWords.projection (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) .simultaneous
abbrev advance := SourceGeneratedActionWords.advance (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) .simultaneous
abbrev readout := SourceGeneratedActionWords.readout (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) .simultaneous
abbrev originalRestriction := SourceGeneratedActionWords.originalRestriction
  (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) .simultaneous
theorem advance_source (letter : Letter) (value : Carrier root recognition visit successor) :
    advance root recognition visit successor transition alignment U7 calculus count letter
      (projection root recognition visit successor transition alignment U7 calculus count value) =
        projection root recognition visit successor transition alignment U7 calculus count
          (actions root recognition visit successor transition alignment U7 calculus count letter value) :=
  SourceGeneratedActionWords.advance_source _ _ _ _ _

theorem readout_source (word : List Letter) (value : Carrier root recognition visit successor) :
    readout root recognition visit successor transition alignment U7 calculus count word
      (projection root recognition visit successor transition alignment U7 calculus count value) =
        read root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word value) :=
  SourceGeneratedActionWords.readout_source _ _ _ _ _

theorem full_fibre (left right : Carrier root recognition visit successor) :
    projection root recognition visit successor transition alignment U7 calculus count left =
      projection root recognition visit successor transition alignment U7 calculus count right ↔
        ∀ word : List Letter, read root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word left) =
        read root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word right) :=
  SourceGeneratedActionWords.projection_fibre _ _ _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
