import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
abbrev step := recognition.generateStepAt visit
abbrev Source := Σ pairing : PairingAt recognition.material.parent (step root recognition visit).sourceOccurrence,
  RawExposureAt (H:=H) recognition.material.parent (step root recognition visit).sourceOccurrence pairing
abbrev Target := Σ pairing : PairingAt recognition.material.parent successor.targetOccurrence,
  RawExposureAt (H:=H) recognition.material.parent successor.targetOccurrence pairing
def sourceTree : RootedAccountedUnfolding (Source root recognition visit) :=
  (stepSourcePairingOccurrence (step root recognition visit)).map (fun pairing => ⟨pairing,stepSourceExposureAt (step root recognition visit) pairing⟩)
def targetTree : RootedAccountedUnfolding (Target root recognition visit successor) :=
  (stepTargetPairingOccurrence (step root recognition visit) successor).map (fun pairing => ⟨pairing,stepTargetExposureAt (step root recognition visit) successor pairing⟩)
abbrev SourceActor := {actor : Source root recognition visit // actor ∈ (sourceTree root recognition visit).trace}
abbrev TargetActor := {actor : Target root recognition visit successor // actor ∈ (targetTree root recognition visit successor).trace}
inductive Letter where
 | source (actor : SourceActor root recognition visit)
 | target (actor : TargetActor root recognition visit successor)
 | simultaneous
abbrev Carrier := SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Carrier root recognition visit successor
variable (transition : GeneratedStepJointTransitionAt (step root recognition visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt (stepSourcePairingOccurrence (step root recognition visit))
  (stepTargetPairingOccurrence (step root recognition visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)
def actions : Letter root recognition visit successor → Carrier root recognition visit successor →ₗ[ℤ] Carrier root recognition visit successor
 | .source actor => actor.val.2.sourceAction.carrierAction.prodMap LinearMap.id
 | .target actor => LinearMap.id.prodMap actor.val.2.sourceAction.carrierAction
 | .simultaneous => SourceOperationNative.Tree.Fold.Dependent.Joint.normedAction root visit recognition successor transition alignment U7 calculus count
abbrev coarseRead := SourceOperationNative.Tree.Fold.Dependent.Joint.normedObservation root visit recognition successor transition alignment U7 calculus count
def sourceObservation : Carrier root recognition visit successor →ₗ[ℤ] (SourceActor root recognition visit → H) :=
  LinearMap.pi (fun actor => actor.val.2.measurement.comp (LinearMap.fst ℤ _ _))
def targetObservation : Carrier root recognition visit successor →ₗ[ℤ] (TargetActor root recognition visit successor → H) :=
  LinearMap.pi (fun actor => actor.val.2.measurement.comp (LinearMap.snd ℤ _ _))
def read := (coarseRead root recognition visit successor transition alignment U7 calculus count).prod
  ((sourceObservation root recognition visit successor).prod (targetObservation root recognition visit successor))
abbrev CoarseModel := SourceGeneratedActionWords.Model (actions root recognition visit successor transition alignment U7 calculus count)
  (coarseRead root recognition visit successor transition alignment U7 calculus count) .simultaneous
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

theorem full_fibre (left right : Carrier root recognition visit successor) :
    projection root recognition visit successor transition alignment U7 calculus count left =
      projection root recognition visit successor transition alignment U7 calculus count right ↔
        ∀ word : List (Letter root recognition visit successor),
          read root recognition visit successor transition alignment U7 calculus count
            (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word left) =
          read root recognition visit successor transition alignment U7 calculus count
            (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word right) :=
  SourceGeneratedActionWords.projection_fibre _ _ _ _ _

def sourceRootActor : SourceActor root recognition visit :=
  ⟨(sourceTree root recognition visit).root,RootedAccountedUnfolding.root_mem_trace _⟩
def targetRootActor : TargetActor root recognition visit successor :=
  ⟨(targetTree root recognition visit successor).root,RootedAccountedUnfolding.root_mem_trace _⟩

def embed : SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Letter.{u} → Letter root recognition visit successor
 | .source => .source (sourceRootActor root recognition visit)
 | .target => .target (targetRootActor root recognition visit successor)
 | .simultaneous => .simultaneous

theorem source_root_action : (sourceRootActor root recognition visit).val.2.sourceAction.carrierAction =
    (stepSourceExposure (step root recognition visit)).sourceAction.carrierAction := by
  exact congrArg (fun datum : Source root recognition visit => datum.2.sourceAction.carrierAction)
    (RootedAccountedUnfolding.root_map _ _)
theorem target_root_action : (targetRootActor root recognition visit successor).val.2.sourceAction.carrierAction =
    (stepTargetExposure (step root recognition visit) successor).sourceAction.carrierAction := by
  exact congrArg (fun datum : Target root recognition visit successor => datum.2.sourceAction.carrierAction)
    (RootedAccountedUnfolding.root_map _ _)

theorem embed_action (letter : SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Letter.{u}) :
    actions root recognition visit successor transition alignment U7 calculus count (embed root recognition visit successor letter) =
      SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.actions root recognition visit successor transition alignment U7 calculus count letter := by
  cases letter with
  | simultaneous => rfl
  | source =>
      change (sourceRootActor root recognition visit).val.2.sourceAction.carrierAction.prodMap LinearMap.id = _
      rw [source_root_action]
      have source := congrArg (fun packet : SourceHistoryCommon.Root.Action.Plan root visit recognition successor => packet.source.sourceAction.carrierAction)
        (SourceOperationNative.Tree.Fold.Dependent.Joint.action_packet_generated root visit recognition successor transition alignment U7 calculus count)
      exact congrArg (fun action => action.prodMap (LinearMap.id : (StepTargetHistory (step root recognition visit) successor).CompletionCarrier →ₗ[ℤ] _)) source.symm
  | target =>
      change LinearMap.id.prodMap (targetRootActor root recognition visit successor).val.2.sourceAction.carrierAction = _
      rw [target_root_action]
      have target := congrArg (fun packet : SourceHistoryCommon.Root.Action.Plan root visit recognition successor => packet.target.sourceAction.carrierAction)
        (SourceOperationNative.Tree.Fold.Dependent.Joint.action_packet_generated root visit recognition successor transition alignment U7 calculus count)
      exact congrArg (fun action => (LinearMap.id : (StepSourceHistory (step root recognition visit)).CompletionCarrier →ₗ[ℤ] _).prodMap action) target.symm
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
