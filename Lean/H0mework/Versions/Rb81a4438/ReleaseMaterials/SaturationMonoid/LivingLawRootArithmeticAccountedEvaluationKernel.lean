import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawArithmeticAccountedEvaluationKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticHomologicalCompletionKernel

/-!
# Root-controlled accounted arithmetic evaluation

The exact root homological face already owns the complex, process, whole
ledger and generated next.  Evaluation is derived from that face as an
unfolding fold.  This module adds no evaluation authority token, scalar field,
pairing matrix, measure, branch or successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticAccountedEvaluation

open ArithmeticAccountedEvaluation
open ArithmeticFreeClosure
open ArithmeticGeneration
open ArithmeticHomologicalCompletion
open RootArithmeticCompletion
open RootArithmeticHomologicalCompletion
open RootArithmeticIncidence
open RootArithmeticProcess
open RootedAccountedUnfolding

universe u v

/-- Evaluation exposure derived from the exact root-owned complex. -/
def evaluationUnfoldingAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process)
    (depth : UnitHistory) :
    RootedAccountedUnfolding ResidualEvaluationPoint :=
  ArithmeticAccountedEvaluation.evaluationUnfolding
    homological.boundaryComplex depth

/-- Image readout; the caller supplies only an ordinary hypothetical-fibre
observer algebra, never root authority or a target value. -/
def evaluationImageAt
    {Carrier : Type v}
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (depth : UnitHistory) : Carrier :=
  accountedEvaluation homological.boundaryComplex seed advance depth

theorem evaluationImageAt_eq_observationFold
    {Carrier : Type v}
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (depth : UnitHistory) :
    evaluationImageAt homological seed advance depth =
      residualObservationFold homological.boundaryComplex seed advance depth :=
  accountedEvaluation_eq_residualObservationFold
    homological.boundaryComplex seed advance depth

/-- The responsibility readout is the derived nonempty frontier. -/
theorem evaluationResponsibilityAt_ne_nil
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process)
    (depth : UnitHistory) :
    (evaluationUnfoldingAt homological depth).frontier ≠ [] :=
  RootedAccountedUnfolding.frontier_ne_nil _

/-- Boundary-of-boundary evaluation is zero at every generated state. -/
def boundarySquareEvaluationAt
    {Carrier : Type v} [Zero Carrier]
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process)
    (state : ResidualTriangleState) : Carrier :=
  boundarySquareEvaluation (Carrier := Carrier)
    (homological.boundaryComplex.boundarySquareAt state)

@[simp] theorem boundarySquareEvaluationAt_eq_zero
    {Carrier : Type v} [Zero Carrier]
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process)
    (state : ResidualTriangleState) :
    boundarySquareEvaluationAt (Carrier := Carrier) homological state = 0 :=
  boundarySquareEvaluation_eq_zero _

/-- Evaluation reuses the existing root whole-ledger write-back. -/
def evaluationWholeLedgerWriteBack
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process) :=
  homological.wholeLedgerWriteBack

/-- Evaluation cannot choose the next current. -/
def evaluationNextCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  homological.nextCurrent

@[simp] theorem evaluationNextCurrent_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (homological : RootGeneratedArithmeticHomologicalCompletionAt process) :
    evaluationNextCurrent homological = root.generatedNextCurrentAt visit :=
  homological.nextCurrent_eq

end RootArithmeticAccountedEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
