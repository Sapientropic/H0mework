import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Evaluator.Installation
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
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (no_refill wellFounded activePayment)
end P
open RootGeneratedCofinalFaithfulRealizationAt

def OutputAt (phase : ResidualDispositionOutcome (face root visit recognition successor)) : Type u :=
  match phase with
  | .faithful _sound _coverage _proof => (R.common root visit recognition successor).CompletionCarrier ≃+ Value root visit recognition successor
  | .unsound _ _coordinate => GeneratedRelationResidualCoordinateAt (face root visit recognition successor)
  | .kernelResidual sound _ _coordinate => GeneratedKernelResidualCoordinateAt (face root visit recognition successor) sound
  | .coverageResidual sound _ _coordinate => GeneratedCoverageResidualCoordinateAt (face root visit recognition successor) sound

def generatedOutput : OutputAt root visit recognition successor (disposition root visit recognition successor) := by
  generalize selected_eq : disposition root visit recognition successor = selected
  cases selected with
  | faithful sound coverage proof => exact proof.canonicalQuotientAddEquiv
  | unsound obstruction coordinate => exact coordinate
  | kernelResidual sound obstruction coordinate => exact coordinate
  | coverageResidual sound obstruction coordinate => exact coordinate

theorem normal : O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) =
    Finsupp.single (combine root visit recognition successor (source root visit recognition) (target root visit recognition successor)) 1 :=
  (O.value_source root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).trans
    (SourceNativeBinary.lift_point _ _ _)

theorem cost : (O.trace root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).length = 3 :=
  (O.paid_history root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).trans (by rfl)

abbrev payment (count : Fin 3) := P.activePayment root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)
  ⟨count.1, by exact count.2⟩

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem source_material (count : Nat) : (materialFace root visit recognition successor U7 calculus count).rootRead.1.1 =
    source root visit recognition := rfl

theorem target_material (count : Nat) : (materialFace root visit recognition successor U7 calculus count).rootRead.1.2 =
    target root visit recognition successor := rfl

theorem disposition_material (count : Nat) : (materialFace root visit recognition successor U7 calculus count).rootRead.2.1.2 =
    disposition root visit recognition successor := rfl

abbrev recoveredFace (count : Nat) := RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=R.common root visit recognition successor)
  (evaluatorOccurrence:=(materialFace root visit recognition successor U7 calculus count).rootRead.2.1.1)
theorem actual_source_word (count : Nat) (word : R.G root recognition →₀ ℤ) :
    ((recoveredFace root visit recognition successor U7 calculus count).freeEvaluation word).down.1 =
      (sourceFace root visit recognition).freeEvaluation word := source_word root visit recognition successor word

theorem actual_target_word (count : Nat) (word : R.G root recognition →₀ ℤ) :
    ((recoveredFace root visit recognition successor U7 calculus count).freeEvaluation word).down.2 =
      (targetFace root visit recognition successor).freeEvaluation word := target_word root visit recognition successor word

namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) ∧
    type_of% (M.activated_answer (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) ∧
    type_of% (M.activated_next (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) :=
  ⟨M.activated_query (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset,
    M.activated_answer (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset,
    M.activated_next (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset⟩
theorem parent_next (count : Nat) : type_of%
    (SourceTemporalMaterial.Calculation.parent_next_preserved
      (sourceRoot root visit recognition successor) (sourceVisit root visit recognition successor) U7 calculus
      (installedReader root visit recognition successor) count) :=
  SourceTemporalMaterial.Calculation.parent_next_preserved
    (sourceRoot root visit recognition successor) (sourceVisit root visit recognition successor) U7 calculus
    (installedReader root visit recognition successor) count

theorem all_stage_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (actualRoot root visit recognition successor).toAuthoritativeRoot visit.current
      (installedReader root visit recognition successor) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition successor).toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor) count
end SourceHistoryCommon.Root.Evaluator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
