import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Common
import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Evaluator.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
open RootInquiryCompletion SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
variable (U7' : U7ProducerCalculus N) (calculus' : U7ObstructionEvolutionCalculus N U7')
theorem evaluator_raw : (sourceOutcome root visit recognition successor transition alignment).2.2.2.1 =
    SourceHistoryCommon.Root.Evaluator.combine root visit recognition successor
      (SourceHistoryCommon.Root.Evaluator.source root visit recognition)
      (SourceHistoryCommon.Root.Evaluator.target root visit recognition successor) := by
  unfold sourceOutcome
  cases tree root visit recognition successor transition alignment
  rfl

abbrev evaluatorPacket (count : Nat) :=
  ((face root visit recognition successor transition alignment U7' calculus' count).rootRead.1.fold
    (constructor root visit recognition successor transition)).2.2.2.1

theorem evaluator_packet_generated (count : Nat) : evaluatorPacket root visit recognition successor transition alignment U7' calculus' count =
    SourceHistoryCommon.Root.Evaluator.combine root visit recognition successor
      (SourceHistoryCommon.Root.Evaluator.source root visit recognition)
      (SourceHistoryCommon.Root.Evaluator.target root visit recognition successor) :=
  evaluator_raw root visit recognition successor transition alignment

abbrev evaluatorFace (count : Nat) := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=commonRead root visit recognition successor transition alignment U7' calculus' count)
  (evaluatorOccurrence:=evaluatorPacket root visit recognition successor transition alignment U7' calculus' count)
abbrev evaluatorDisposition (count : Nat) := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual
  (evaluatorFace root visit recognition successor transition alignment U7' calculus' count)
theorem evaluator_source_word (count : Nat) (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :
    ((evaluatorFace root visit recognition successor transition alignment U7' calculus' count).freeEvaluation word).down.1 =
      (SourceHistoryCommon.Root.Evaluator.sourceFace root visit recognition).freeEvaluation word := by
  classical
  induction word using Finsupp.induction with
  | zero => simp only [map_zero]; rfl
  | @single_add generator integer rest absent nonzero previous =>
    rw [map_add, CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single,
      map_add, CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single]
    change integer • ((evaluatorPacket root visit recognition successor transition alignment U7' calculus' count).root generator).down.1 +
      ((evaluatorFace root visit recognition successor transition alignment U7' calculus' count).freeEvaluation rest).down.1 = _
    have basis := congrArg (fun packet : SourceHistoryCommon.Root.Evaluator.Result root visit recognition successor =>
      integer • (packet.root generator).down.1)
        (evaluator_packet_generated root visit recognition successor transition alignment U7' calculus' count)
    exact congrArg₂ (· + ·) basis previous

theorem evaluator_target_word (count : Nat) (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :
    ((evaluatorFace root visit recognition successor transition alignment U7' calculus' count).freeEvaluation word).down.2 =
      (SourceHistoryCommon.Root.Evaluator.targetFace root visit recognition successor).freeEvaluation word := by
  classical
  induction word using Finsupp.induction with
  | zero => simp only [map_zero]; rfl
  | @single_add generator integer rest absent nonzero previous =>
    rw [map_add, CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single,
      map_add, CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single]
    change integer • ((evaluatorPacket root visit recognition successor transition alignment U7' calculus' count).root generator).down.2 +
      ((evaluatorFace root visit recognition successor transition alignment U7' calculus' count).freeEvaluation rest).down.2 = _
    have basis := congrArg (fun packet : SourceHistoryCommon.Root.Evaluator.Result root visit recognition successor =>
      integer • (packet.root generator).down.2)
        (evaluator_packet_generated root visit recognition successor transition alignment U7' calculus' count)
    exact congrArg₂ (· + ·) basis previous
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

def EvaluatorOutputAt (count : Nat) (selected : ResidualDispositionOutcome
    (evaluatorFace root visit recognition successor transition alignment U7' calculus' count)) : Type u :=
  match selected with
  | .faithful _sound _coverage _proof =>
      (commonRead root visit recognition successor transition alignment U7' calculus' count).CompletionCarrier ≃+
        SourceHistoryCommon.Root.Evaluator.Value root visit recognition successor
  | .unsound _ _coordinate => GeneratedRelationResidualCoordinateAt (evaluatorFace root visit recognition successor transition alignment U7' calculus' count)
  | .kernelResidual sound _ _coordinate => GeneratedKernelResidualCoordinateAt (evaluatorFace root visit recognition successor transition alignment U7' calculus' count) sound
  | .coverageResidual sound _ _coordinate => GeneratedCoverageResidualCoordinateAt (evaluatorFace root visit recognition successor transition alignment U7' calculus' count) sound

def evaluatorOutput (count : Nat) : EvaluatorOutputAt root visit recognition successor transition alignment U7' calculus' count
    (evaluatorDisposition root visit recognition successor transition alignment U7' calculus' count) := by
  generalize selected_eq : evaluatorDisposition root visit recognition successor transition alignment U7' calculus' count = selected
  cases selected with
  | faithful sound coverage proof => exact proof.canonicalQuotientAddEquiv
  | unsound obstruction coordinate => exact coordinate
  | kernelResidual sound obstruction coordinate => exact coordinate
  | coverageResidual sound obstruction coordinate => exact coordinate

theorem evaluator_relations_sound_iff (count : Nat) :
    (evaluatorFace root visit recognition successor transition alignment U7' calculus' count).RelationsSound ↔
      (∀ word ∈ (commonRead root visit recognition successor transition alignment U7' calculus' count).relationClosure,
        (SourceHistoryCommon.Root.Evaluator.sourceFace root visit recognition).freeEvaluation word = 0) ∧
      (∀ word ∈ (commonRead root visit recognition successor transition alignment U7' calculus' count).relationClosure,
        (SourceHistoryCommon.Root.Evaluator.targetFace root visit recognition successor).freeEvaluation word = 0) := by
  constructor
  · intro sound
    constructor
    · intro word belongs
      exact (evaluator_source_word root visit recognition successor transition alignment U7' calculus' count word).symm.trans
        (congrArg (fun value : SourceHistoryCommon.Root.Evaluator.Value root visit recognition successor => value.down.1) (sound belongs))
    · intro word belongs
      exact (evaluator_target_word root visit recognition successor transition alignment U7' calculus' count word).symm.trans
        (congrArg (fun value : SourceHistoryCommon.Root.Evaluator.Value root visit recognition successor => value.down.2) (sound belongs))
  · rintro ⟨sourceSound,targetSound⟩ word belongs
    apply ULift.ext
    apply Prod.ext
    · exact (evaluator_source_word root visit recognition successor transition alignment U7' calculus' count word).trans (sourceSound word belongs)
    · exact (evaluator_target_word root visit recognition successor transition alignment U7' calculus' count word).trans (targetSound word belongs)
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
