import H0mework.Versions.R2.Physics.SpinPair.Regularity

/-! The original vacuum and source color doublet close the scalar channel on
the same global actual, including its complete momentum divergence. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeScalarVariation StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation StageNineScalarVariation
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

theorem actual_scalarCovariantDerivative_zero (point : BasePoint) :
    holonomicScalarCovariantDerivative actual point = 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [actual_scalar]
  unfold fieldDirectionalDerivative
  rw [(hasFDerivAt_const (𝕜 := ℝ) (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
    point).fderiv]
  simp only [zero_apply, zero_add, actual_gaugeConnection]
  have spatial (index : Fin 3) :
      scalarMotherLieAction (p286LieBlockEmbed (gaugeScale • sourceColorP286Generator index))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
    rw [p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul,
      sourceColorP286Generator_vacuum_zero, smul_zero]
  fin_cases direction
  · simp [gaugePotential, scalarMotherLieAction, p286LieBlockEmbed_zero]
  · exact spatial 0
  · exact spatial 1
  · exact spatial 2

theorem spinPairDual_yukawa_annihilates
    (scalar : ExteriorBreakingScalarCarrier) (matter : DiracExteriorMatterCarrier) (p q : ℂ) :
    spinPairDual p q (diracDualRightChiralYukawaAction scalar matter) = 0 := by
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state *
    sourceColorDoubletDual state (diracDualRightChiralYukawaAction scalar matter spin)) = 0
  unfold sourceColorDoubletDual diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  unfold diracExteriorYukawaInternalAction internalMatterLinearAction exteriorYukawaInternalAction
  simp

theorem actual_yukawaVector_zero (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField actual point) = 0 := by
  unfold generatedContinuumDiracDualYukawaVector
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm (scalarFrameRelativeCoordinates positiveSmoothUnifiedSource 0 point
      (actual.scalar point)))
    (matterFrameRelative positiveSmoothUnifiedSource 0 point (actual.matter point)) = 0
  rw [actual_scalar, actual_matter, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply]
  unfold diracDualRightChiralYukawaAction
  rw [LinearMap.comp_apply]
  unfold spinPairMatter
  funext spin
  change exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (∑ other, rightChiralityProjector spin other •
      sourceColorDiracMatter (spinPairCoefficients (upperPhase point) (lowerPhase point)) other) = 0
  simp only [sourceColorDiracMatter, map_sum, map_smul,
    sourceColorDoublet_internalYukawa_zero, smul_zero, Finset.sum_const_zero]

theorem actual_scalarKineticFirstVariation_zero
    (point : BasePoint) (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField actual point) variation = 0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  change (1 / 2 : ℝ) * ∑ first, ∑ second,
    ((lorentzianMetricOfCoframe (actual.coframe point))⁻¹ first second) *
      (scalarCoordinatePairingRe
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point variation first)
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point
          (holonomicScalarCovariantDerivative actual point) second) +
       scalarCoordinatePairingRe
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point
          (holonomicScalarCovariantDerivative actual point) first)
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point variation second)) = 0
  rw [actual_scalarCovariantDerivative_zero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem actual_scalarPotentialFirstVariation_zero
    (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
      (toContinuumPointField actual point) variation = 0 := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change 2 * scalarCoordinateRealPairing
    (actual.scalar point - sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) variation = 0
  rw [actual_scalar]
  simp [scalarCoordinateRealPairing]

theorem actual_scalarYukawaFirstVariation_zero
    (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity (toContinuumPointField actual point) variation = 0 := by
  unfold diracDualScalarYukawaFirstVariationDensity diracDualScalarYukawaVariationVector
  change (actual.conjugateMatter point
    (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm variation) (actual.matter point))).re = 0
  rw [actual_conjugateMatter, spinPairDual_yukawa_annihilates]
  rfl

theorem actual_scalarAlgebraic_zero
    (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource actual variation point = 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [actual_scalarKineticFirstVariation_zero, actual_scalarPotentialFirstVariation_zero,
    actual_scalarYukawaFirstVariation_zero]
  simp

theorem actual_scalarMomentum_zero
    (variation : ScalarCoordinateCarrier) (direction : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource actual variation direction = 0 := by
  funext point
  unfold scalarDifferentialMomentum
  rw [actual_scalarKineticFirstVariation_zero]
  simp

theorem actual_scalarEuler_zero
    (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource actual variation point = 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient scalarDifferentialMomentumDivergence
  simp only [actual_scalarAlgebraic_zero, actual_scalarMomentum_zero]
  simp [fieldDirectionalDerivative]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
