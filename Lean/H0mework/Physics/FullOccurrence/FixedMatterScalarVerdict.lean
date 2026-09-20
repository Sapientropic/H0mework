import H0mework.Physics.FullOccurrence.FixedP286Verdict

/-!
# Fixed P506/L0 full-occurrence global matter--scalar verdict

The source/current-only full-occurrence operator has already generated one
global actual `U6`.  On the fixed P506/L0 lineage, all primitive fields read
by the scalar, primal-matter, and adjoint-matter Euler channels agree with the
previous action-generated live-electric `PreEC` actual.  In particular, the
Lorentz connection equality is the unconditional whole-field theorem already
proved for `U6`, not a supplied pointwise seam.

This module unfolds those three mother-action readers and proves their exact
all-point equality.  It consumes no residual, support coordinate, target jet,
branch, or zero-fiber receipt.  The result removes the full-occurrence and EC
tails from the three final reads; whether the retained `PreEC` reads vanish
away from the fixed origin remains a separate direct calculation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterScalarVerdict

open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterVariation
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginMatterAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginScalarClosure
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineP286GaugeConnectionActionVariation
open StageNineScalarPointwiseEquation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev PreEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

/-! ## Exact primitive-field alignment -/

private theorem u6_coframe_eq_preEC : U6.coframe = PreEC.coframe := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).coframe = PreEC.coframe
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source U5).trans
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC

private theorem u6_gravityConnection_eq_preEC :
    U6.gravityConnection = PreEC.gravityConnection :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC

private theorem u6_gaugeConnection_eq_preEC :
    U6.gaugeConnection = PreEC.gaugeConnection :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current.trans
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC

private theorem u6_scalar_eq_preEC : U6.scalar = PreEC.scalar := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).scalar = PreEC.scalar
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source U5).trans
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC

private theorem u6_matter_eq_preEC : U6.matter = PreEC.matter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).matter = PreEC.matter
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
      Source U5).trans
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC

private theorem u6_conjugateMatter_eq_preEC :
    U6.conjugateMatter = PreEC.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).conjugateMatter = PreEC.conjugateMatter
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
      Source U5).trans
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC

/-! ## Scalar read -/

private theorem u6_scalarCovariantDerivative_eq_preEC :
    holonomicScalarCovariantDerivative U6 =
      holonomicScalarCovariantDerivative PreEC := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [u6_scalar_eq_preEC, u6_gaugeConnection_eq_preEC]

private theorem u6_scalarDifferentialMomentum_eq_preEC
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source U6 direction derivativeDirection =
      scalarDifferentialMomentum Source PreEC direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_preEC, u6_scalarCovariantDerivative_eq_preEC]

private theorem u6_scalarDifferentialMomentumDivergence_eq_preEC
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source U6 direction =
      scalarDifferentialMomentumDivergence Source PreEC direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [u6_scalarDifferentialMomentum_eq_preEC]

private theorem u6_scalarAlgebraic_eq_preEC
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient Source U6 direction point =
      diracDualScalarAlgebraicDirectionalCoefficient Source PreEC direction point := by
  have variationEquality :
      holonomicScalarVariationAlgebraicDirection U6 direction point =
        holonomicScalarVariationAlgebraicDirection PreEC direction point := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [u6_gaugeConnection_eq_preEC]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_preEC, u6_scalar_eq_preEC,
    u6_scalarCovariantDerivative_eq_preEC, u6_matter_eq_preEC,
    u6_conjugateMatter_eq_preEC, variationEquality]

/-! ## Primal-matter read -/

private theorem u6_matterDifferentialMomentum_eq_preEC
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum Source U6 direction derivativeDirection =
      matterDifferentialMomentum Source PreEC direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_preEC, u6_conjugateMatter_eq_preEC]

private theorem u6_matterDifferentialMomentumDivergence_eq_preEC
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source U6 direction =
      matterDifferentialMomentumDivergence Source PreEC direction := by
  funext point
  unfold matterDifferentialMomentumDivergence
  simp_rw [u6_matterDifferentialMomentum_eq_preEC]

private theorem u6_matterAlgebraic_eq_preEC
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualMatterAlgebraicDirectionalCoefficient Source U6 direction point =
      diracDualMatterAlgebraicDirectionalCoefficient Source PreEC direction point := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection U6 direction point =
        holonomicMatterVariationAlgebraicDirection PreEC direction point := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [u6_gravityConnection_eq_preEC, u6_gaugeConnection_eq_preEC]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_preEC, u6_scalar_eq_preEC,
    u6_conjugateMatter_eq_preEC, variationEquality]

/-! ## Adjoint-matter read -/

private theorem u6_matterCovariantDerivative_eq_preEC
    (point : BasePoint) :
    holonomicMatterCovariantDerivative U6 point =
      holonomicMatterCovariantDerivative PreEC point := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [u6_matter_eq_preEC, u6_gravityConnection_eq_preEC,
    u6_gaugeConnection_eq_preEC]

private theorem u6_generatedMatterVector_eq_preEC
    (point : BasePoint) :
    generatedContinuumDiracDualMatterVector Source 0 point
        (toContinuumPointField U6 point) =
      generatedContinuumDiracDualMatterVector Source 0 point
        (toContinuumPointField PreEC point) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_preEC, u6_matterCovariantDerivative_eq_preEC,
    u6_scalar_eq_preEC, u6_matter_eq_preEC]

/-! ## Three unconditional all-point verdicts -/

/-- The final scalar Euler read on `U6` is exactly the retained `PreEC` read
at every spacetime point. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_scalarResidual_eq_preEC
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point).scalar =
      (diracDualFormNativePointwiseJointResidual Source PreEC point).scalar := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source U6 direction point =
      diracDualScalarEulerLagrangeDirectionalCoefficient Source PreEC direction point
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [u6_scalarAlgebraic_eq_preEC,
    congrFun (u6_scalarDifferentialMomentumDivergence_eq_preEC direction) point]

/-- The final primal-matter Euler read on `U6` is exactly the retained
`PreEC` read at every spacetime point.  No connection-equality premise is
needed: the fixed whole-field equality was generated upstream. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_eq_preEC
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point).matter =
      (diracDualFormNativePointwiseJointResidual Source PreEC point).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source U6 direction point =
      diracDualMatterEulerLagrangeDirectionalCoefficient Source PreEC direction point
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [u6_matterAlgebraic_eq_preEC,
    congrFun (u6_matterDifferentialMomentumDivergence_eq_preEC direction) point]

/-- The independent adjoint-matter Euler read on `U6` has the same exact
all-point `PreEC` value. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_eq_preEC
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual Source PreEC point).conjugateMatter := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source U6 direction point =
      diracDualConjugateMatterDirectionalCoefficient Source PreEC direction point
  unfold diracDualConjugateMatterDirectionalCoefficient generatedVolumeDensity
  change
    |Matrix.det (U6.coframe point)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector Source 0 point
            (toContinuumPointField U6 point))).re =
      |Matrix.det (PreEC.coframe point)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector Source 0 point
            (toContinuumPointField PreEC point))).re
  rw [u6_coframe_eq_preEC, u6_generatedMatterVector_eq_preEC]

/-- At the fixed source occurrence the three transported reads therefore
inhabit their common zero fiber on the same generated `U6`.  This is the
concrete zero-value specialization of the all-point verdicts above; it does
not extend the origin receipt away from that occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterScalar_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source U6 0).scalar = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source U6 0).matter = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source U6 0).conjugateMatter = 0 := by
  constructor
  · rw [
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_scalarResidual_eq_preEC]
    exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_origin_zero
  constructor
  · rw [
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_eq_preEC]
    exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_origin_zero
  · rw [
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_eq_preEC]
    exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterScalarVerdict
