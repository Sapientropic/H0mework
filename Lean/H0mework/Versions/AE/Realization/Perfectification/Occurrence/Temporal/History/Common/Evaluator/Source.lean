import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.RootSource
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Root.Evaluator
open SourceOperationEffects SourceOperationExecution CofinalFaithfulRealization
open RootLawDependentJointStateController RootLawDependentJointTransition
namespace R
export SourceHistoryCommon.Root (step common G)
end R
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (R.step root visit recognition))
abbrev law := recognition.material.parent.commonLaw
abbrev source := (law root recognition).evaluatorOccurrenceAt (R.step root visit recognition).sourceOccurrence
abbrev target := (law root recognition).evaluatorOccurrenceAt successor.targetOccurrence
abbrev SourceValue := ((law root recognition).complexAt (R.step root visit recognition).sourceOccurrence).root.X 0
abbrev TargetValue := ((law root recognition).complexAt successor.targetOccurrence).root.X 0
abbrev Value := ULift.{u} (SourceValue root visit recognition × TargetValue root visit recognition successor)
def combine (first : type_of% (source root visit recognition)) (second : type_of% (target root visit recognition successor)) :
    RootedAccountedUnfolding (R.G root recognition → Value root visit recognition successor) :=
  RootedAccountedUnfolding.parallelAt (fun generator => ⟨first.root generator, second.root generator⟩)
    (first.map (fun evaluator generator => ⟨evaluator generator, second.root generator⟩))
    (second.map (fun evaluator generator => ⟨first.root generator, evaluator generator⟩))
abbrev face := RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=R.common root visit recognition successor) (evaluatorOccurrence:=combine root visit recognition successor (source root visit recognition) (target root visit recognition successor))
abbrev disposition := RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual (face root visit recognition successor)
theorem actual_basis (generator : R.G root recognition) (integer : ℤ) :
    (face root visit recognition successor).freeEvaluation (Finsupp.single generator integer) =
      integer • (ULift.up ((source root visit recognition).root generator, (target root visit recognition successor).root generator)) :=
  RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single _ _ _
abbrev sourceFace := (law root recognition).faithfulAt (R.step root visit recognition).sourceOccurrence
abbrev targetFace := (law root recognition).faithfulAt successor.targetOccurrence

theorem source_word (word : R.G root recognition →₀ ℤ) :
    ((face root visit recognition successor).freeEvaluation word).down.1 =
      (sourceFace root visit recognition).freeEvaluation word := by
  classical
  induction word using Finsupp.induction with
  | zero => simp only [map_zero]; rfl
  | @single_add generator integer rest absent nonzero previous =>
    rw [map_add, RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single,
      map_add, RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single]
    change integer • (source root visit recognition).root generator +
      ((face root visit recognition successor).freeEvaluation rest).down.1 = _
    rw [previous]
    rfl

theorem target_word (word : R.G root recognition →₀ ℤ) :
    ((face root visit recognition successor).freeEvaluation word).down.2 =
      (targetFace root visit recognition successor).freeEvaluation word := by
  classical
  induction word using Finsupp.induction with
  | zero => simp only [map_zero]; rfl
  | @single_add generator integer rest absent nonzero previous =>
    rw [map_add, RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single,
      map_add, RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single]
    change integer • (target root visit recognition successor).root generator +
      ((face root visit recognition successor).freeEvaluation rest).down.2 = _
    rw [previous]
    rfl
theorem relations_sound_iff : (face root visit recognition successor).RelationsSound ↔
    (∀ word ∈ (R.common root visit recognition successor).relationClosure,
      (sourceFace root visit recognition).freeEvaluation word = 0) ∧
    (∀ word ∈ (R.common root visit recognition successor).relationClosure,
      (targetFace root visit recognition successor).freeEvaluation word = 0) := by
  constructor
  · intro sound
    constructor
    · intro word belongs
      exact (source_word root visit recognition successor word).symm.trans
        (congrArg (fun value : Value root visit recognition successor => value.down.1) (sound belongs))
    · intro word belongs
      exact (target_word root visit recognition successor word).symm.trans
        (congrArg (fun value : Value root visit recognition successor => value.down.2) (sound belongs))
  · rintro ⟨sourceSound,targetSound⟩ word belongs
    apply ULift.ext
    apply Prod.ext
    · exact (source_word root visit recognition successor word).trans (sourceSound word belongs)
    · exact (target_word root visit recognition successor word).trans (targetSound word belongs)
abbrev SourceInput := type_of% (source root visit recognition)
abbrev TargetInput := type_of% (target root visit recognition successor)
abbrev Result := RootedAccountedUnfolding (R.G root recognition → Value root visit recognition successor)
abbrev Slot := ULift.{u} SourceNativeBinary.BinarySort
abbrev NativeValue : Slot.{u} → Type u := fun slot => SourceNativeBinary.Value
  (SourceInput root visit recognition) (TargetInput root visit recognition successor) (Result root visit recognition successor) slot.down
abbrev NativeVar : Slot.{u} → Type u := fun slot => SourceNativeBinary.Var
  (SourceInput root visit recognition) (TargetInput root visit recognition successor) (Result root visit recognition successor) slot.down
instance : (slot : Slot.{u}) → AddCommGroup (NativeValue root visit recognition successor slot) :=
  fun slot => SourceNativeBinary.instAddCommGroupValue slot.down

def environment : Env (NativeValue root visit recognition successor) (NativeVar root visit recognition successor) :=
  fun slot datum => SourceNativeBinary.environment slot.down datum

def expression : Expr (NativeValue root visit recognition successor) (NativeVar root visit recognition successor) (ULift.up .result) :=
  .bilinear (s:=ULift.up .left) (t:=ULift.up .right) (SourceNativeBinary.lift (combine root visit recognition successor))
    (.var (source root visit recognition)) (.var (target root visit recognition successor))

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=NativeValue root visit recognition successor) (Var:=NativeVar root visit recognition successor) (sort:=ULift.up .result) :=
  ⟨environment root visit recognition successor, expression root visit recognition successor⟩
def reader (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) := raw root visit recognition successor
end SourceHistoryCommon.Root.Evaluator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
