import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words
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

def family : (Covariance.Actor root recognition visit successor → H) →ₗ[ℤ] Space root recognition visit successor :=
  (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).symm.toLinearMap.comp
    (LinearMap.pi (fun index => LinearMap.proj (actor root recognition visit successor index)))
def wordEvolution : List (Letter root recognition visit successor) → Space root recognition visit successor →ₗᵢ[ℂ] Space root recognition visit successor
  | [] => LinearIsometry.id
  | letter::rest => (wordEvolution rest).comp (evolution root recognition visit successor letter)
theorem evolution_family (letter : Letter root recognition visit successor)
    (values : Covariance.Actor root recognition visit successor → H) :
    evolution root recognition visit successor letter (family root recognition visit successor values) =
      family root recognition visit successor (EffectHistory.wave root recognition visit successor letter values) := by
  apply (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).injective
  funext index
  exact wave_node root recognition visit successor letter index values

theorem word_family (word : List (Letter root recognition visit successor))
    (values : Covariance.Actor root recognition visit successor → H) :
    wordEvolution root recognition visit successor word (family root recognition visit successor values) =
      family root recognition visit successor
        (SourceGeneratedActionWords.run (EffectHistory.wave root recognition visit successor) word values) := by
  induction word generalizing values with
  | nil => rfl
  | cons letter rest previous =>
    change wordEvolution root recognition visit successor rest
      (evolution root recognition visit successor letter (family root recognition visit successor values)) = _
    rw [evolution_family,previous]
    rfl

def action (word : List (Letter root recognition visit successor)) : SourceGeneratedIntegralCoherentCovariance.ActionData
    (measurement root recognition visit successor transition alignment U7 calculus count) where
  integralTransition := SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) word
  hilbertEvolution := wordEvolution root recognition visit successor word
abbrev effect (word : List (Letter root recognition visit successor)) (value : Model root recognition visit successor transition alignment U7 calculus count) :=
  SourceGeneratedIntegralCoherentCovariance.couplingResidual
    (action root recognition visit successor transition alignment U7 calculus count word) value

theorem effect_source (word : List (Letter root recognition visit successor))
    (point : Carrier root recognition visit successor) :
    effect root recognition visit successor transition alignment U7 calculus count word
      (projection root recognition visit successor transition alignment U7 calculus count point) =
    family root recognition visit successor (EffectHistory.total root recognition visit successor transition alignment U7 calculus count point word) := by
  change wordEvolution root recognition visit successor word
      (family root recognition visit successor (EffectHistory.measurement root recognition visit successor transition alignment U7 calculus count
        (projection root recognition visit successor transition alignment U7 calculus count point))) -
      family root recognition visit successor (EffectHistory.measurement root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) word
          (projection root recognition visit successor transition alignment U7 calculus count point))) = _
  rw [word_family,SourceGeneratedActionWords.run_source,← map_sub]
  rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
