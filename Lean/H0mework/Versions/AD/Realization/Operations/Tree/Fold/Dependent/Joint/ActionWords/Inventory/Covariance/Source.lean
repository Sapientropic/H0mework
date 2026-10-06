import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NextInput
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
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
abbrev Actor := SourceActor root recognition visit ⊕ TargetActor root recognition visit successor
abbrev SourceValues := SourceActor root recognition visit → H
abbrev TargetValues := TargetActor root recognition visit successor → H

def feature : Actor root recognition visit successor → Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] H
  | .inl actor => (LinearMap.proj actor).comp
      ((LinearMap.fst ℤ (SourceValues root recognition visit) (TargetValues root recognition visit successor)).comp
        ((LinearMap.snd ℤ (Joint.commonRead root visit recognition successor transition alignment U7 calculus count).CompletionCarrier
          (SourceValues root recognition visit × TargetValues root recognition visit successor)).comp
            (readout root recognition visit successor transition alignment U7 calculus count [])))
  | .inr actor => (LinearMap.proj actor).comp
      ((LinearMap.snd ℤ (SourceValues root recognition visit) (TargetValues root recognition visit successor)).comp
        ((LinearMap.snd ℤ (Joint.commonRead root visit recognition successor transition alignment U7 calculus count).CompletionCarrier
          (SourceValues root recognition visit × TargetValues root recognition visit successor)).comp
            (readout root recognition visit successor transition alignment U7 calculus count [])))

def letter : Actor root recognition visit successor → Letter root recognition visit successor
  | .inl actor => .source actor
  | .inr actor => .target actor

def evolution : Actor root recognition visit successor → H →ₗᵢ[ℂ] H
  | .inl actor => actor.val.2.hilbertEvolution
  | .inr actor => actor.val.2.hilbertEvolution

def originalFeature : Actor root recognition visit successor → Carrier root recognition visit successor →ₗ[ℤ] H
  | .inl actor => actor.val.2.measurement.comp (LinearMap.fst ℤ _ _)
  | .inr actor => actor.val.2.measurement.comp (LinearMap.snd ℤ _ _)

variable (actor : Actor root recognition visit successor)
def action : SourceGeneratedIntegralCoherentCovariance.ActionData
    (feature root recognition visit successor transition alignment U7 calculus count actor) where
  integralTransition := advance root recognition visit successor transition alignment U7 calculus count (letter root recognition visit successor actor)
  hilbertEvolution := evolution root recognition visit successor actor

abbrev effect (value : Model root recognition visit successor transition alignment U7 calculus count) :=
  SourceGeneratedIntegralCoherentCovariance.couplingResidual
    (action root recognition visit successor transition alignment U7 calculus count actor) value

variable (point : Carrier root recognition visit successor)
theorem feature_source : feature root recognition visit successor transition alignment U7 calculus count actor
    (projection root recognition visit successor transition alignment U7 calculus count point) =
      originalFeature root recognition visit successor actor point := by
  have given := SourceGeneratedActionWords.readout_source
    (actions root recognition visit successor transition alignment U7 calculus count)
    (read root recognition visit successor transition alignment U7 calculus count)
    (.simultaneous : Letter root recognition visit successor) [] point
  cases actor with
  | inl original => exact congrArg (fun value => value.2.1 original) given
  | inr original => exact congrArg (fun value => value.2.2 original) given

theorem effect_source : effect root recognition visit successor transition alignment U7 calculus count actor
    (projection root recognition visit successor transition alignment U7 calculus count point) =
      evolution root recognition visit successor actor (originalFeature root recognition visit successor actor point) -
        originalFeature root recognition visit successor actor
          (actions root recognition visit successor transition alignment U7 calculus count (letter root recognition visit successor actor) point) := by
  change evolution root recognition visit successor actor (feature _ _ _ _ _ _ _ _ _ actor (projection _ _ _ _ _ _ _ _ _ point)) -
    feature _ _ _ _ _ _ _ _ _ actor
      (advance _ _ _ _ _ _ _ _ _ (letter _ _ _ _ actor) (projection _ _ _ _ _ _ _ _ _ point)) = _
  rw [SourceGeneratedActionWords.advance_source,feature_source,feature_source]

abbrev disposition := SourceGeneratedIntegralCoherentCovariance.settleCovariance
  (action root recognition visit successor transition alignment U7 calculus count actor)

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
