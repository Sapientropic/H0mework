import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawArithmeticHomologicalCompletionKernel

/-!
# Accounted evaluation as an unfolding fold

Evaluation is not a seventh arithmetic constructor and does not produce a
receipt record.  A finite residual observation is exposed as one rooted tree;
its image is the universal fold, its direction is the tree root, and its
unresolved responsibility is the derived frontier.

The construction factors the existing observation fold through the universal
one-constructor kernel.  The generated `d² = 0` normal form likewise evaluates
to zero by folding that exact normal form, not by accepting a target scalar.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ArithmeticAccountedEvaluation

open ArithmeticFreeClosure
open ArithmeticGeneration
open ArithmeticHomologicalCompletion
open RootedAccountedUnfolding

universe u

/-- Directions of the observation calculation.  They are fold coordinates,
not occurrence constructors. -/
inductive ResidualEvaluationPoint : Type
  | seed
  | boundary (state : ResidualTriangleState)
  deriving DecidableEq

/-- Finite evaluation exposure, ordered so the newest boundary folds over the
already generated prior observation. -/
def evaluationUnfolding
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target) :
    UnitHistory → RootedAccountedUnfolding ResidualEvaluationPoint
  | .empty => zero .seed
  | .next prior =>
      .occur (.boundary (complex.stateAfter prior)) <|
        .singleton (evaluationUnfolding complex prior)

private def firstChildOr {Carrier : Type u}
    (fallback : Carrier) : List Carrier → Carrier
  | [] => fallback
  | first :: _ => first

/-- Local observation algebra.  The seed and boundary action determine the
entire readout; no value, fibre or completed observation table is stored. -/
def evaluationAlgebra
    {Carrier : Type u}
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (point : ResidualEvaluationPoint)
    (children : List Carrier) : Carrier :=
  match point with
  | .seed => seed
  | .boundary state =>
      advance (complex.boundaryKindAt state) (firstChildOr seed children)

/-- Image of the accountable fold. -/
def accountedEvaluation
    {Carrier : Type u}
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (depth : UnitHistory) : Carrier :=
  (evaluationUnfolding complex depth).fold
    (evaluationAlgebra complex seed advance)

@[simp] theorem accountedEvaluation_empty
    {Carrier : Type u}
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier) :
    accountedEvaluation complex seed advance .empty = seed :=
  rfl

@[simp] theorem accountedEvaluation_next
    {Carrier : Type u}
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (prior : UnitHistory) :
    accountedEvaluation complex seed advance (.next prior) =
      advance (complex.boundaryKindAt (complex.stateAfter prior))
        (accountedEvaluation complex seed advance prior) :=
  rfl

/-- The historical observation evaluator is exactly the image of the
one-constructor fold. -/
theorem accountedEvaluation_eq_residualObservationFold
    {Carrier : Type u}
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (seed : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (depth : UnitHistory) :
    accountedEvaluation complex seed advance depth =
      residualObservationFold complex seed advance depth := by
  induction depth with
  | empty => rfl
  | next prior inductionHypothesis =>
      rw [accountedEvaluation_next]
      change
        advance (complex.boundaryKindAt (complex.stateAfter prior))
            (accountedEvaluation complex seed advance prior) =
          advance (complex.boundaryKindAt (complex.stateAfter prior))
            (residualObservationFold complex seed advance prior)
      exact congrArg
        (advance (complex.boundaryKindAt (complex.stateAfter prior)))
        inductionHypothesis

/-- The direction readout is derived from the evaluation occurrence. -/
def evaluationDirection
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (depth : UnitHistory) : ResidualEvaluationPoint :=
  (evaluationUnfolding complex depth).root

/-- The responsibility readout is the actual open frontier, not a field of a
receipt record. -/
def evaluationResponsibility
    {source target : DerivedArithmeticOccurrence}
    (complex : SourceGeneratedResidualBoundaryComplexAt source target)
    (depth : UnitHistory) : List ResidualEvaluationPoint :=
  (evaluationUnfolding complex depth).frontier

/-- Exact boundary-square normal form as a one-node exposure. -/
def boundarySquareUnfolding
    {source target : DerivedArithmeticOccurrence}
    {complex : SourceGeneratedResidualBoundaryComplexAt source target}
    {state : ResidualTriangleState}
    (square : SourceGeneratedResidualBoundarySquareAt complex state) :
    RootedAccountedUnfolding ResidualBoundaryCompositeNormalForm :=
  zero square.normalForm

/-- Evaluation of the generated composite normal form. -/
def boundarySquareEvaluation
    {Carrier : Type u} [Zero Carrier]
    {source target : DerivedArithmeticOccurrence}
    {complex : SourceGeneratedResidualBoundaryComplexAt source target}
    {state : ResidualTriangleState}
    (square : SourceGeneratedResidualBoundarySquareAt complex state) : Carrier :=
  (boundarySquareUnfolding square).fold fun normalForm _children =>
    match normalForm with
    | .zero => 0

/-- Stokes/`d² = 0` readout: the image is zero because the exact generated
composite normal form is zero.  Zero is a theorem, not a stored result. -/
@[simp] theorem boundarySquareEvaluation_eq_zero
    {Carrier : Type u} [Zero Carrier]
    {source target : DerivedArithmeticOccurrence}
    {complex : SourceGeneratedResidualBoundaryComplexAt source target}
    {state : ResidualTriangleState}
    (square : SourceGeneratedResidualBoundarySquareAt complex state) :
    boundarySquareEvaluation (Carrier := Carrier) square = 0 :=
  rfl

/-- Process normalization is now literally the same exposure, so every
accounted evaluation commutes with compilation. -/
theorem normalize_fold_commutes
    {Carrier : Type u}
    (algebra : DerivedArithmeticDirection → List Carrier → Carrier)
    (occurrence : DerivedArithmeticOccurrence) :
    RootedAccountedUnfolding.fold algebra
        (ArithmeticProcess.normalize occurrence) =
      RootedAccountedUnfolding.fold algebra occurrence :=
  rfl

end ArithmeticAccountedEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
