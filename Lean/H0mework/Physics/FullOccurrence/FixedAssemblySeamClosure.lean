import H0mework.Physics.FullOccurrence.FixedGravityCurvatureSeam
import H0mework.Physics.FullOccurrence.FixedResidualNormalForm

/-!
# Fixed P506/L0 full-occurrence global assembly-seam closure

The source/current-only full-occurrence operator has already produced one
four-dimensional actual.  This module computes its exhaustive action-jet
assembly seam against the matching five-leg contact.

The gravity-auxiliary exterior-covariant derivative closes identically on
the whole generated spacetime: the global auxiliary is the same `II+`
field, its directional derivative is the translated contact derivative, and
both reads use the same generated connection value.  The remaining
coordinates stay in one whole-carrier normal form.  No seam coordinate,
residual support, branch, or target jet enters a writer here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalResidualNormalForm
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricKinematics
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

/-! ## Diagonal primitive normal form -/

/-- The occurrence-diagonal scalar keeps the supplied whole scalar field.
The local scalar acceleration is a second primitive anchored at the contact
origin, so it changes the contact jet but not the assembled point value. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).scalar =
      current.scalar := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar_eq_existing]
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source (fullyRecenterHolonomicConfiguration current point)).scalar 0 =
      current.scalar point
  simp [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
    canonicalTimeSecondPrimitive]

/-- The occurrence-diagonal primal matter field likewise keeps the supplied
whole point-value field; the action-selected temporal correction remains in
the contact jet for the seam read. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).matter =
      current.matter := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter_eq_existing]
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source (fullyRecenterHolonomicConfiguration current point)).matter 0 =
      current.matter point
  simp [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
    canonicalTimePrimitive]

/-- The same point-value law holds for the adjoint matter field. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).conjugateMatter =
      current.conjugateMatter := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter_eq_existing]
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source (fullyRecenterHolonomicConfiguration current point)
      ).conjugateMatter 0 =
      current.conjugateMatter point
  simp [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
    canonicalTimePrimitive]

/-! ## Derived-jet seam -/

private theorem contact_gravityAuxiliary_eq_recenteredIIPlus
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (completeJointLiveElectricECFullOccurrenceContact source current
      point).gravityAuxiliary =
      (fun candidate => physicalIIPlusBivector (current.coframe candidate)) ∘
        canonicalSpacetimeContactTranslation point := by
  funext localPoint
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
      source (fullyRecenterHolonomicConfiguration current point)
      ).gravityAuxiliary localPoint = _
  unfold
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity]
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing]
  rw [sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe]
  rfl

private theorem global_gravityAuxiliaryDirectionalDerivative_eq_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    gravityAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
          source current) point =
      gravityAuxiliaryDirectionalDerivative
        (completeJointLiveElectricECFullOccurrenceContact source current point)
        0 := by
  funext direction
  unfold gravityAuxiliaryDirectionalDerivative
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary,
    contact_gravityAuxiliary_eq_recenteredIIPlus,
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simp

/-- The gravity-auxiliary derivative coordinate of the exhaustive seam
vanishes at every occurrence of the fixed source/current global write.  This
is a whole-spacetime naturality result, not a contact-origin convention. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
    (point : BasePoint) :
    (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
      point).gravityAuxiliaryExteriorCovariantDerivative =
      0 := by
  change
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
          Source Current) point -
      holonomicGravityAuxiliaryExteriorCovariantDerivative
        (completeJointLiveElectricECFullOccurrenceContact Source Current point)
        0 =
      0
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_at]
  rw [global_gravityAuxiliaryDirectionalDerivative_eq_contact]
  exact sub_self _

/-- Exact whole-carrier normal form of the eight-coordinate assembly seam.
The gravity coordinate is the difference between the curvature of the
already generated pre-EC global actual and the matching action-generated EC
target.  The gravity-auxiliary derivative closes identically; the other six
coordinates remain literal reads of the same generated seam. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam_normalForm
    (point : BasePoint) :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
        point =
      { gravityCurvature :=
          holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
              point -
            sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
              Source
              (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
                Source
                (fullyRecenterHolonomicConfiguration Current point))
        gaugeCurvature :=
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
            point).gaugeCurvature
        scalarCovariantDerivative :=
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
            point).scalarCovariantDerivative
        matterCovariantDerivative :=
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
            point).matterCovariantDerivative
        gravityAuxiliaryExteriorCovariantDerivative := 0
        p286GaugeAuxiliaryExteriorCovariantDerivative :=
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
            point).p286GaugeAuxiliaryExteriorCovariantDerivative
        scalarDifferentialMomentumDivergence :=
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
            point).scalarDifferentialMomentumDivergence
        matterDifferentialMomentumDivergence :=
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
            point).matterDifferentialMomentumDivergence } := by
  apply CompleteJointActionJetAssemblySeam.ext
  all_goals first
    | rfl
    | exact
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam_gravityCurvature_eq_preEC_sub_target
          point
    | exact
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
          point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
