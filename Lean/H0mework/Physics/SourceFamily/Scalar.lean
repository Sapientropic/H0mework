import H0mework.Physics.SourceGauge.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Scalar

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeScalarVariation StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation StageNineScalarVariation
open Stage9C.Material.SpinPair
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction SU7MotherGaugeTheory

noncomputable section

theorem yukawa_vector_zero (step : ℕ) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector (sourceAt step) 0 point
      (toContinuumPointField (fieldAt step) point) = 0 := by
  unfold generatedContinuumDiracDualYukawaVector
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm (scalarFrameRelativeCoordinates (sourceAt step) 0 point
      ((fieldAt step).scalar point)))
    (matterFrameRelative (sourceAt step) 0 point ((fieldAt step).matter point)) = 0
  rw [Gauge.field_scalar, Gauge.field_matter, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, vacuum_retained, Runtime.source_eq]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply]
  unfold diracDualRightChiralYukawaAction
  rw [LinearMap.comp_apply]
  unfold spinPairMatter
  funext spin
  change exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (∑ other, rightChiralityProjector spin other •
      sourceColorDiracMatter (spinPairCoefficients (Gauge.upper step point) (Gauge.lower step point)) other) = 0
  simp only [sourceColorDiracMatter, map_sum, map_smul,
    sourceColorDoublet_internalYukawa_zero, smul_zero, Finset.sum_const_zero]

theorem potential_first_variation_zero
    (step : ℕ) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation (sourceAt step)
      (toContinuumPointField (fieldAt step) point) variation = 0 := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change 2 * scalarCoordinateRealPairing
    ((fieldAt step).scalar point - sourceGeneratedVacuumCoordinates (sourceAt step)) variation = 0
  rw [Gauge.field_scalar]
  simp [scalarCoordinateRealPairing]

theorem yukawa_first_variation_zero
    (step : ℕ) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity
      (toContinuumPointField (fieldAt step) point) variation = 0 := by
  unfold diracDualScalarYukawaFirstVariationDensity diracDualScalarYukawaVariationVector
  change ((fieldAt step).conjugateMatter point
    (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm variation)
      ((fieldAt step).matter point))).re = 0
  rw [Gauge.field_dual, spinPairDual_yukawa_annihilates]
  rfl

theorem algebraic_zero
    (step : ℕ) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient (sourceAt step) (fieldAt step) variation point = 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [Gauge.scalar_gauge_coefficient_zero, potential_first_variation_zero,
    yukawa_first_variation_zero]
  simp

theorem momentum_zero
    (step : ℕ) (variation : ScalarCoordinateCarrier) (direction : LorentzianIndex) :
    scalarDifferentialMomentum (sourceAt step) (fieldAt step) variation direction = 0 := by
  funext point
  unfold scalarDifferentialMomentum
  rw [Gauge.scalar_gauge_coefficient_zero]
  simp

theorem euler_zero
    (step : ℕ) (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient
      (sourceAt step) (fieldAt step) variation point = 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient scalarDifferentialMomentumDivergence
  simp only [algebraic_zero, momentum_zero]
  simp [fieldDirectionalDerivative]

theorem residual_zero (step : ℕ) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual (sourceAt step) (fieldAt step) point).scalar = 0 :=
  funext (euler_zero step point)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Scalar
