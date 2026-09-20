import H0mework.Physics.ConstrainedCauchy.FixedJointDirectPrimitivePath
import H0mework.Physics.ConstrainedCauchy.FixedDirectPrefixQuadraticCoframeBoundary
import H0mework.Physics.ConstrainedCauchy.FixedExponentialGlobalOperator

/-!
# Fixed exponential Cauchy direct complete-joint output

This module specializes the existing direct complete-joint occurrence to the
fixed P506/L0 exponential Cauchy current.  It records the exact three-leg
action write, the globally nondegenerate section prefix, and the geometric
acceptance laws of the emitted output.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialCompleteJointDirectPrimitivePath

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialGlobalOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialCauchyGlobalActual

/-- Complete-joint spacetime section emitted from the exponential Cauchy
current before the radial primitive write. -/
def fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePathPrefix :
    StageNineHolonomicConfiguration :=
  directPrimitivePathPrefix Source Current

/-- Exact fixed source/current occurrence of the generic three-leg direct
complete-joint writer. -/
def fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathOccurrence :
    CompleteJointDirectPrimitivePathOccurrence Source Current :=
  sourceActionGeneratedCompleteJointDirectPrimitivePathOccurrence
    Source Current

/-- Final output of the same fixed occurrence. -/
def fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathOccurrence.finalActual

private abbrev Prefix : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePathPrefix

private abbrev Occurrence :
    CompleteJointDirectPrimitivePathOccurrence Source Current :=
  fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathOccurrence

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual

/-- Every leg is the native action write of this exact occurrence. -/
theorem
    fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathOccurrence_after_eq_actionWrite
    (leg : CompleteJointDirectPrimitivePathWriteLeg) :
    Occurrence.after leg =
      completeJointDirectPrimitivePathActionWrite Source leg
        (Occurrence.before leg) :=
  Occurrence.after_eq_actionWrite leg

theorem
    fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual_eq_actionOperator :
    Output =
      sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
        positiveSmoothUnifiedSource
        fixedP506L0CartanECConstraintExponentialCauchyGlobalActual :=
  rfl

/-- The complete-joint section preserves the globally invertible exponential
coframe before the radial primitive write. -/
theorem
    fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePathPrefix_nondegenerate :
    Prefix.Nondegenerate := by
  intro point
  change Matrix.det
    ((sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      Source Current).coframe point) ≠ 0
  rw [sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe]
  exact
    fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_nondegenerate
      point

/-- At the source-generated quadratic singular point, the quadratic coframe
has zero determinant and the exponential direct prefix is nondegenerate. -/
theorem
    fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePath_closes_quadraticBoundary :
    Matrix.det
          (fixedP506L0CartanECConstraintPreparedActual.coframe
            fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint) =
        0 ∧
      Matrix.det
          (Prefix.coframe
            fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint) ≠
        0 := by
  exact
    ⟨fixedP506L0CartanECConstraintPreparedActual_determinant_zero,
      fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePathPrefix_nondegenerate
        fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint⟩

theorem
    fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation Output :=
  sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_simplicity
    Source Current

theorem
    fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation Output :=
  sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_auxiliaryEquation
    Source Current

theorem
    fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual_reactionSelfGenerated :
    Output.gravitySimplicityMultiplier =
      formNativeGravityReactionField Output :=
  sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_reactionSelfGenerated
    Source Current

theorem
    fixedP506L0CartanECConstraintExponentialCauchyCompleteJointDirectPrimitivePathGlobalActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialCompleteJointDirectPrimitivePath
