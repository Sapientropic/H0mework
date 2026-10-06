import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Targets
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Next.Material
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
abbrev step := recognition.generateStepAt visit
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
abbrev nextVisit := visit.next successor.next_eq
abbrev Token := Σ current, root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current
def targetToken : Token root := ⟨successor.targetCurrent,successor.targetOccurrence⟩
def emittedNextToken : Token root := ⟨(nextVisit root visit recognition successor).current,root.emitted (nextVisit root visit recognition successor).current⟩
def nextToken : Token root := ⟨(nextVisit root visit recognition successor).current,
  (step root (nextVisit root visit recognition successor) recognition).sourceOccurrence⟩
theorem next_token_emitted : nextToken root visit recognition successor = emittedNextToken root visit recognition successor :=
  congrArg (fun occurrence => (⟨(nextVisit root visit recognition successor).current,occurrence⟩ : Token root))
    (step root (nextVisit root visit recognition successor) recognition).parentStep.commonStep.generated.occurrence_eq
theorem token_eq : targetToken root visit recognition successor = nextToken root visit recognition successor :=
  (congrArg (fun occurrence => (⟨successor.targetCurrent,occurrence⟩ : Token root))
    (successor_targetOccurrence_eq_emitted (step root visit recognition) successor)).trans
      (next_token_emitted root visit recognition successor).symm

abbrev G := recognition.material.parent.commonLaw.historyLaw.Generator
def generatorsAt (token : Token root) : Submodule ℤ (G root recognition →₀ ℤ) :=
  (recognition.material.parent.commonLaw.historyAt token.2).generatorClosure
def relationsAt (token : Token root) : Submodule ℤ (G root recognition →₀ ℤ) :=
  (recognition.material.parent.commonLaw.historyAt token.2).relationClosure

theorem generators_square :
    generatorsAt root recognition (targetToken root visit recognition successor) =
      generatorsAt root recognition (nextToken root visit recognition successor) :=
  congrArg (generatorsAt root recognition) (token_eq root visit recognition successor)

theorem relations_square :
    relationsAt root recognition (targetToken root visit recognition successor) =
      relationsAt root recognition (nextToken root visit recognition successor) :=
  congrArg (relationsAt root recognition) (token_eq root visit recognition successor)

theorem target_generators_next_source :
    (StepTargetHistory (step root visit recognition) successor).generatorClosure =
      (StepSourceHistory (step root (nextVisit root visit recognition successor) recognition)).generatorClosure := by
  have square := generators_square root visit recognition successor
  dsimp only [generatorsAt,targetToken,nextToken] at square
  exact square

theorem target_relations_next_source :
    (StepTargetHistory (step root visit recognition) successor).relationClosure =
      (StepSourceHistory (step root (nextVisit root visit recognition successor) recognition)).relationClosure := by
  have square := relations_square root visit recognition successor
  dsimp only [relationsAt,targetToken,nextToken] at square
  exact square
abbrev WordAt (token : Token root) := generatorsAt root recognition token

def wordAtNext : WordAt root recognition (targetToken root visit recognition successor) →ₗ[ℤ]
    WordAt root recognition (nextToken root visit recognition successor) :=
  (LinearEquiv.ofEq _ _ (generators_square root visit recognition successor)).toLinearMap

theorem word_at_next_val (word : WordAt root recognition (targetToken root visit recognition successor)) :
    (wordAtNext root visit recognition successor word).val = word.val :=
  LinearEquiv.coe_ofEq_apply (generators_square root visit recognition successor) word

def wordFromTarget (word : SourceOperationNative.Tree.Fold.Dependent.Joint.Transport.TargetWord root visit recognition successor) :
    WordAt root recognition (targetToken root visit recognition successor) := by
  refine ⟨word.val,?_⟩
  dsimp only [WordAt,generatorsAt,targetToken]
  exact word.property

def wordToNextSource (word : WordAt root recognition (nextToken root visit recognition successor)) :
    SourceOperationNative.Tree.Fold.Dependent.Joint.Transport.SourceWord root (nextVisit root visit recognition successor) recognition := by
  refine ⟨word.val,?_⟩
  simpa only [WordAt,generatorsAt,nextToken] using word.property

def generatedNextWord (word : SourceOperationNative.Tree.Fold.Dependent.Joint.Transport.TargetWord root visit recognition successor) :=
  wordToNextSource root visit recognition successor
    (wordAtNext root visit recognition successor (wordFromTarget root visit recognition successor word))

theorem generated_next_word_value (word : SourceOperationNative.Tree.Fold.Dependent.Joint.Transport.TargetWord root visit recognition successor) :
    (generatedNextWord root visit recognition successor word).val = word.val :=
  word_at_next_val root visit recognition successor (wordFromTarget root visit recognition successor word)
def pairingAtToken (token : Token root) : PairingAt recognition.material.parent token.2 :=
  (recognition.material.parent.pairingAt token.2).root
abbrev ExposureAtToken (token : Token root) := RawExposureAt (H:=H) recognition.material.parent token.2
  (pairingAtToken root recognition token)
def exposureAtToken (token : Token root) : ExposureAtToken root recognition token :=
  recognition.material.exposureAt token.2 (pairingAtToken root recognition token)
def exposurePacket (token : Token root) : Σ token : Token root, ExposureAtToken root recognition token :=
  ⟨token,exposureAtToken root recognition token⟩

theorem exposure_square : HEq (exposureAtToken root recognition (targetToken root visit recognition successor))
    (exposureAtToken root recognition (nextToken root visit recognition successor)) :=
  (Sigma.mk.inj (congrArg (exposurePacket root recognition) (token_eq root visit recognition successor))).2

theorem original_exposure_next : HEq (stepTargetExposure (step root visit recognition) successor)
    (stepSourceExposure (step root (nextVisit root visit recognition successor) recognition)) := by
  have square := exposure_square root visit recognition successor
  dsimp only [exposureAtToken,pairingAtToken,targetToken,nextToken] at square
  exact square
abbrev ExposureTreeAtToken (token : Token root) := RootedAccountedUnfolding
  (Σ pairing : PairingAt recognition.material.parent token.2,
    RawExposureAt (H:=H) recognition.material.parent token.2 pairing)
def exposureTreeAtToken (token : Token root) : ExposureTreeAtToken root recognition token :=
  (recognition.material.parent.pairingAt token.2).map (fun pairing => ⟨pairing,recognition.material.exposureAt token.2 pairing⟩)
def exposureTreePacket (token : Token root) : Σ token : Token root, ExposureTreeAtToken root recognition token :=
  ⟨token,exposureTreeAtToken root recognition token⟩

theorem full_exposure_square : HEq (exposureTreeAtToken root recognition (targetToken root visit recognition successor))
    (exposureTreeAtToken root recognition (nextToken root visit recognition successor)) :=
  (Sigma.mk.inj (congrArg (exposureTreePacket root recognition) (token_eq root visit recognition successor))).2
end SourceOperationNative.Tree.Fold.Dependent.Next.Material
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
