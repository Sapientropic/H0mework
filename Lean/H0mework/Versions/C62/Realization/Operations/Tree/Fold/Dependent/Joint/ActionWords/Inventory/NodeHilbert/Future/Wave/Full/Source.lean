import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Full.Map
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullOrbit
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

abbrev Family := (bound : Nat) → Space root recognition visit successor bound
def waveAction (letter : Letter root recognition visit successor) :
    Family root recognition visit successor →ₗ[ℤ] Family root recognition visit successor :=
  LinearMap.pi (fun bound => ((evolution root recognition visit successor bound letter).toLinearMap.restrictScalars ℤ).comp (LinearMap.proj bound))
def read : Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] Family root recognition visit successor :=
  LinearMap.pi (Future.observation root recognition visit successor transition alignment U7 calculus count)
def input : SourceGeneratedJointActionWords.Input
    (Letter root recognition visit successor)
    (Model root recognition visit successor transition alignment U7 calculus count)
    (Family root recognition visit successor)
    (CoarseModel root recognition visit successor transition alignment U7 calculus count) where
 integralAction := Inventory.advance root recognition visit successor transition alignment U7 calculus count
 coherentAction := waveAction root recognition visit successor
 measurementAction := Recovery.coarseAdvance root recognition visit successor transition alignment U7 calculus count
 coherentRead := read root recognition visit successor transition alignment U7 calculus count
 measurementRead := coarseRestriction root recognition visit successor transition alignment U7 calculus count
abbrev FullCarrier := (input root recognition visit successor transition alignment U7 calculus count).Carrier
abbrev advance := (input root recognition visit successor transition alignment U7 calculus count).advance
abbrev seed := (input root recognition visit successor transition alignment U7 calculus count).seedLift

def restriction (bound : Nat) : FullCarrier root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    PaidSourceWordOrbit.WordCarrier root recognition visit successor transition alignment U7 calculus count bound :=
  (input root recognition visit successor transition alignment U7 calculus count).carrierMap
    (LinearMap.proj bound) (fun letter => (evolution root recognition visit successor bound letter).toLinearMap.restrictScalars ℤ)
      (fun _ _ => rfl)
theorem restriction_seed (bound : Nat) (event : Model root recognition visit successor transition alignment U7 calculus count) :
    restriction root recognition visit successor transition alignment U7 calculus count bound
      (seed root recognition visit successor transition alignment U7 calculus count event)=
      PaidSourceWordOrbit.seed root recognition visit successor transition alignment U7 calculus count bound event := rfl
theorem restriction_advance (bound : Nat) (letter : Letter root recognition visit successor)
    (value : FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    restriction root recognition visit successor transition alignment U7 calculus count bound
      (advance root recognition visit successor transition alignment U7 calculus count letter value)=
      PaidSourceWordOrbit.advance root recognition visit successor transition alignment U7 calculus count bound letter
        (restriction root recognition visit successor transition alignment U7 calculus count bound value) := rfl
theorem wave_word_cell (letters : List (Letter root recognition visit successor))
    (value : Family root recognition visit successor) (bound : Nat) :
    SourceGeneratedActionWords.run (waveAction root recognition visit successor) letters value bound=
      wordEvolution root recognition visit successor bound letters (value bound) := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous => exact previous (waveAction root recognition visit successor first value)
theorem wave_restriction_word (bound : Nat) (letters : List (Letter root recognition visit successor))
    (value : Space root recognition visit successor (bound+1)) :
    Future.restriction root recognition visit successor bound
      (wordEvolution root recognition visit successor (bound+1) letters value)=
      wordEvolution root recognition visit successor bound letters (Future.restriction root recognition visit successor bound value) := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous =>
    exact (previous (evolution root recognition visit successor (bound+1) first value)).trans
      (congrArg (wordEvolution root recognition visit successor bound rest)
        (restriction_wave root recognition visit successor bound first value))
theorem ambient_family (letters : List (Letter root recognition visit successor))
    (value : (input root recognition visit successor transition alignment U7 calculus count).Ambient)
    (bound : Nat) :
    (SourceGeneratedActionWords.run (input root recognition visit successor transition alignment U7 calculus count).ambientAction letters value).2.1 bound=
      wordEvolution root recognition visit successor bound letters (value.2.1 bound) := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous => exact previous ((input root recognition visit successor transition alignment U7 calculus count).ambientAction first value)
theorem family_generator (letters : List (Letter root recognition visit successor))
    (event : Model root recognition visit successor transition alignment U7 calculus count) (bound : Nat) :
    ((input root recognition visit successor transition alignment U7 calculus count).generator (letters,event)).2.1 bound=
      wordEvolution root recognition visit successor bound letters
        (Future.observation root recognition visit successor transition alignment U7 calculus count bound event) :=
  ambient_family root recognition visit successor transition alignment U7 calculus count letters
    ((input root recognition visit successor transition alignment U7 calculus count).seed event) bound
def coherentData : SourceGeneratedScalarCofinalKernelCompletion.Data (R:=ℤ)
    (Generator:=FullCarrier root recognition visit successor transition alignment U7 calculus count)
    (Carrier:=Space root recognition visit successor) where
  evaluator := fun bound => (LinearMap.proj bound).comp
    (input root recognition visit successor transition alignment U7 calculus count).coherentFace
  transition := Future.restriction root recognition visit successor

theorem coherent_compatible : (coherentData root recognition visit successor transition alignment U7 calculus count).Compatible := by
  intro bound
  apply LinearMap.ext
  intro value
  change Future.restriction root recognition visit successor bound (value.1.2.1 (bound+1))=value.1.2.1 bound
  refine Submodule.span_induction (p:=fun candidate _ => Future.restriction root recognition visit successor bound (candidate.2.1 (bound+1))=candidate.2.1 bound) ?_ ?_ ?_ ?_ value.2
  · rintro _ ⟨⟨letters,event⟩,rfl⟩
    rw [family_generator,family_generator]
    exact wave_restriction_word root recognition visit successor bound letters
      (Future.observation root recognition visit successor transition alignment U7 calculus count (bound+1) event)
  · rfl
  · intro left right _ _ hl hr
    change Future.restriction root recognition visit successor bound (left.2.1 (bound+1)+right.2.1 (bound+1))=left.2.1 bound+right.2.1 bound
    rw [map_add,hl,hr]
  · intro coefficient point _ hp
    change Future.restriction root recognition visit successor bound (coefficient • point.2.1 (bound+1))=coefficient • point.2.1 bound
    rw [map_smul,hp]
abbrev coherentWhole := (coherentData root recognition visit successor transition alignment U7 calculus count).Completion
  (coherent_compatible root recognition visit successor transition alignment U7 calculus count)
abbrev coherentSourceMap := ((coherentData root recognition visit successor transition alignment U7 calculus count).completionMap
  (coherent_compatible root recognition visit successor transition alignment U7 calculus count)).hom
def coherentMorphism (letter : Letter root recognition visit successor) : SourceGeneratedScalarCofinalNaturality.Morphism
    (coherentData root recognition visit successor transition alignment U7 calculus count)
    (coherentData root recognition visit successor transition alignment U7 calculus count) where
 generatorMap := advance root recognition visit successor transition alignment U7 calculus count letter
 stageMap := fun bound => (evolution root recognition visit successor bound letter).toLinearMap.restrictScalars ℤ
 transition_naturality := fun bound => by
   apply LinearMap.ext
   intro value
   exact (restriction_wave root recognition visit successor bound letter value).symm
 evaluator_naturality := fun _ => by
   apply LinearMap.ext
   intro value
   rfl
abbrev coherentAdvance (letter : Letter root recognition visit successor) :=
  ((coherentMorphism root recognition visit successor transition alignment U7 calculus count letter).completionMorphism
    (coherent_compatible root recognition visit successor transition alignment U7 calculus count)
    (coherent_compatible root recognition visit successor transition alignment U7 calculus count)).hom
theorem coherent_source (letter : Letter root recognition visit successor)
    (value : FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    coherentAdvance root recognition visit successor transition alignment U7 calculus count letter
      (coherentSourceMap root recognition visit successor transition alignment U7 calculus count value)=
      coherentSourceMap root recognition visit successor transition alignment U7 calculus count
        (advance root recognition visit successor transition alignment U7 calculus count letter value) :=
  CategoryTheory.ConcreteCategory.congr_hom
    ((coherentMorphism root recognition visit successor transition alignment U7 calculus count letter).completionMorphism_source_naturality
      (coherent_compatible root recognition visit successor transition alignment U7 calculus count)
      (coherent_compatible root recognition visit successor transition alignment U7 calculus count)) value

theorem exact_future (bound : Nat) (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (input root recognition visit successor transition alignment U7 calculus count).coherentFace
      ((input root recognition visit successor transition alignment U7 calculus count).incidence letters value) bound=
      Wave.effect root recognition visit successor transition alignment U7 calculus count bound letters value :=
  (congrArg (fun family => family bound)
    ((input root recognition visit successor transition alignment U7 calculus count).incidence_coherent letters value)).trans
      (congrArg (fun measured => measured-Future.observation root recognition visit successor transition alignment U7 calculus count bound
        (SourceGeneratedActionWords.run (Inventory.advance root recognition visit successor transition alignment U7 calculus count) letters value))
        (wave_word_cell root recognition visit successor letters (read root recognition visit successor transition alignment U7 calculus count value) bound))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
