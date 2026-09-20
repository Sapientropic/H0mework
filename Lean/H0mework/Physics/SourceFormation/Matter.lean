import H0mework.Physics.SourceFormation.Transport

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.Matter

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDiracDualFormNativeMatterVariation StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open Stage9C.Material.SpinPair

noncomputable section

theorem covariant_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    holonomicMatterCovariantDerivative (formedField source) point =
      holonomicMatterCovariantDerivative (SourceFamily.fieldAt (index source)) point := by
  unfold holonomicMatterCovariantDerivative
  rw [matter_eq, gravity_connection_eq, gauge_connection_eq]

theorem kinetic_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    generatedContinuumMatterKineticVector source 0 point
      (toContinuumPointField (formedField source) point) =
      generatedContinuumMatterKineticVector (SourceFamily.sourceAt (index source)) 0 point
        (toContinuumPointField (SourceFamily.fieldAt (index source)) point) := by
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField, coframe_eq, covariant_eq]

theorem algebraic_eq (source : SmoothUnifiedSource) (point : BasePoint)
    (variation : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient source (formedField source) variation point =
      diracDualMatterAlgebraicDirectionalCoefficient (SourceFamily.sourceAt (index source))
        (SourceFamily.fieldAt (index source)) variation point := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
  simp only [dual_eq, SourceFamily.Gauge.field_dual, map_add, spinPairDual_yukawa_annihilates, add_zero]
  unfold matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    holonomicMatterVariationAlgebraicDirection generatedVolumeDensity
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField, coframe_eq,
    gravity_connection_eq, gauge_connection_eq]

theorem momentum_eq (source : SmoothUnifiedSource) (variation : MatterCoordinateCarrier)
    (direction : LorentzianIndex) :
    matterDifferentialMomentum source (formedField source) variation direction =
      matterDifferentialMomentum (SourceFamily.sourceAt (index source))
        (SourceFamily.fieldAt (index source)) variation direction := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector generatedVolumeDensity
  simp only [toContinuumPointField, coframe_eq, dual_eq]

theorem euler_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (variation : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source (formedField source) variation point = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient matterDifferentialMomentumDivergence
  rw [algebraic_eq]
  simp_rw [momentum_eq]
  exact SourceFamily.Dirac.matter_directional_zero (index source) point variation

theorem frozen_kinetic_eq (source : SmoothUnifiedSource) (point : BasePoint)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumMatterKineticDensity source 0 point
      (withCoframe (toContinuumPointField (formedField source) point) candidate) =
      generatedDensitizedContinuumMatterKineticDensity (SourceFamily.sourceAt (index source)) 0 point
        (withCoframe (toContinuumPointField (SourceFamily.fieldAt (index source)) point) candidate) := by
  unfold generatedDensitizedContinuumMatterKineticDensity generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    withCoframe, toContinuumPointField, generatedVolumeDensity, dual_eq, covariant_eq]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.Matter
