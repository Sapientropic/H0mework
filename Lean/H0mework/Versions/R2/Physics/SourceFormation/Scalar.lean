import H0mework.Versions.R2.Physics.SourceFormation.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.Scalar

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeScalarVariation StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity StageNineScalarLocalSpinDensity
open StageNineDiracDualFormNativeJointResidualCarrier StageNineCoframeVariation
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionVariation StageNineScalarPointwiseEquation StageNineScalarVariation
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction SU7ExteriorMatterFullVariations

noncomputable section

private theorem field_scalar (source : SmoothUnifiedSource) :
    (formedField source).scalar = fun _ => sourceGeneratedVacuumCoordinates source := rfl

private theorem field_connection (source : SmoothUnifiedSource) :
    (formedField source).gaugeConnection = fun _ => gaugePotential gaugeScale := rfl

private theorem field_matter (source : SmoothUnifiedSource) :
    (formedField source).matter = (SourceFamily.fieldAt (index source)).matter := by
  rw [SourceFamily.Gauge.field_matter]
  rfl

private theorem field_dual (source : SmoothUnifiedSource) :
    (formedField source).conjugateMatter = (SourceFamily.fieldAt (index source)).conjugateMatter := by
  rw [SourceFamily.Gauge.field_dual]
  rfl

theorem vacuum_scale (source : SmoothUnifiedSource) :
    sourceGeneratedVacuumBase source = (source.stageEight.physicalPhaseAmplitude : ℂ) •
      sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
  rw [positive_sourceGeneratedVacuumBase]
  rfl

theorem vacuum_coordinates_scale (source : SmoothUnifiedSource) :
    sourceGeneratedVacuumCoordinates source = (source.stageEight.physicalPhaseAmplitude : ℂ) •
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  unfold sourceGeneratedVacuumCoordinates
  rw [vacuum_scale source, map_smul]

theorem color_vacuum_zero (source : SmoothUnifiedSource) (direction : Fin 3) :
    scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
      (sourceGeneratedVacuumCoordinates source) = 0 := by
  calc
    _ = scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
        ((source.stageEight.physicalPhaseAmplitude : ℂ) •
          sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) :=
      congrArg (scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction)))
        (vacuum_coordinates_scale source)
    _ = (source.stageEight.physicalPhaseAmplitude : ℂ) •
        scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
      unfold scalarMotherLieAction
      simp only [map_smul]
    _ = 0 := by rw [sourceColorP286Generator_vacuum_zero, smul_zero]

theorem scalar_covariant_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    holonomicScalarCovariantDerivative (formedField source) point = 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [field_scalar]
  unfold fieldDirectionalDerivative
  rw [(hasFDerivAt_const (𝕜 := ℝ) (sourceGeneratedVacuumCoordinates source) point).fderiv]
  simp only [zero_apply, zero_add, field_connection]
  have spatial (direction : Fin 3) :
      scalarMotherLieAction (p286LieBlockEmbed (gaugeScale • sourceColorP286Generator direction))
        (sourceGeneratedVacuumCoordinates source) = 0 := by
    rw [p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul, color_vacuum_zero, smul_zero]
  fin_cases direction
  · simp [gaugePotential, scalarMotherLieAction, p286LieBlockEmbed_zero]
  · exact spatial 0
  · exact spatial 1
  · exact spatial 2

theorem yukawa_vector_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector source 0 point
      (toContinuumPointField (formedField source) point) = 0 := by
  unfold generatedContinuumDiracDualYukawaVector
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm (scalarFrameRelativeCoordinates source 0 point
      ((formedField source).scalar point)))
    (matterFrameRelative source 0 point ((formedField source).matter point)) = 0
  rw [field_scalar, field_matter, SourceFamily.Gauge.field_matter,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply]
  unfold diracDualRightChiralYukawaAction
  rw [LinearMap.comp_apply]
  unfold spinPairMatter
  funext spin
  change exteriorYukawaInternalAction (sourceGeneratedVacuumBase source)
    (∑ other, rightChiralityProjector spin other • sourceColorDiracMatter
      (spinPairCoefficients (SourceFamily.Gauge.upper (index source) point)
        (SourceFamily.Gauge.lower (index source) point)) other) = 0
  rw [vacuum_scale, exteriorYukawaInternalAction_smul]
  simp only [sourceColorDiracMatter, map_sum, map_smul,
    sourceColorDoublet_internalYukawa_zero, smul_zero, Finset.sum_const_zero,
    LinearMap.smul_apply]

theorem scalar_gauge_coefficient_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField (formedField source) point) variation = 0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  change (1/2:ℝ) * ∑ first, ∑ second,
    ((lorentzianMetricOfCoframe ((formedField source).coframe point))⁻¹ first second) *
      (scalarCoordinatePairingRe (scalarFrameRelativeCovariantDerivative source 0 point variation first)
        (scalarFrameRelativeCovariantDerivative source 0 point
          (holonomicScalarCovariantDerivative (formedField source) point) second) +
       scalarCoordinatePairingRe (scalarFrameRelativeCovariantDerivative source 0 point
          (holonomicScalarCovariantDerivative (formedField source) point) first)
        (scalarFrameRelativeCovariantDerivative source 0 point variation second)) = 0
  rw [scalar_covariant_zero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

private theorem potential_first_variation_zero
    (source : SmoothUnifiedSource) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation source (toContinuumPointField (formedField source) point) variation = 0 := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change 2 * scalarCoordinateRealPairing
    ((formedField source).scalar point - sourceGeneratedVacuumCoordinates source) variation = 0
  rw [field_scalar]
  simp [scalarCoordinateRealPairing]

private theorem yukawa_first_variation_zero
    (source : SmoothUnifiedSource) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity
      (toContinuumPointField (formedField source) point) variation = 0 := by
  unfold diracDualScalarYukawaFirstVariationDensity diracDualScalarYukawaVariationVector
  change ((formedField source).conjugateMatter point
    (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm variation)
      ((formedField source).matter point))).re = 0
  rw [field_dual, SourceFamily.Gauge.field_dual, spinPairDual_yukawa_annihilates]
  rfl

private theorem algebraic_zero
    (source : SmoothUnifiedSource) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient source (formedField source) variation point = 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [scalar_gauge_coefficient_zero, potential_first_variation_zero, yukawa_first_variation_zero]
  simp

private theorem momentum_zero
    (source : SmoothUnifiedSource) (variation : ScalarCoordinateCarrier) (direction : LorentzianIndex) :
    scalarDifferentialMomentum source (formedField source) variation direction = 0 := by
  funext point
  unfold scalarDifferentialMomentum
  rw [scalar_gauge_coefficient_zero]
  simp

theorem euler_zero
    (source : SmoothUnifiedSource) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source (formedField source) variation point = 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient scalarDifferentialMomentumDivergence
  simp only [algebraic_zero, momentum_zero]
  simp [fieldDirectionalDerivative]

theorem residual_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source (formedField source) point).scalar = 0 :=
  funext (euler_zero source point)

theorem frozen_scalar_density_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity source 0 point
      (withCoframe (toContinuumPointField (formedField source) point) candidate) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity generatedScalarPotential
  simp only [withCoframe, toContinuumPointField, scalar_covariant_zero, field_scalar,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart]
  simp [scalarCoordinatePairingRe, scalarCoordinateSquaredNorm]

theorem frozen_yukawa_density_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumDiracDualYukawaDensity source 0 point
      (withCoframe (toContinuumPointField (formedField source) point) candidate) = 0 := by
  have vector : generatedContinuumDiracDualYukawaVector source 0 point
      (withCoframe (toContinuumPointField (formedField source) point) candidate) = 0 := by
    have original := yukawa_vector_zero source point
    unfold generatedContinuumDiracDualYukawaVector at original ⊢
    simpa only [withCoframe] using original
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [vector]
  simp

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.Scalar
