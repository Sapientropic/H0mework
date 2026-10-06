import H0mework.Versions.AB.Physics.MotherSource.GaugeHamiltonian.Energy

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualYukawaLocalSpinDensity
open StageNineMatterVariation StageNineCoframeLocalDifferentiability
open StageNineScalarLocalSpinDensity StageNineDynamicBreakingVacuum
open StageNineFormNativeMotherAction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation
open SU7MotherLieAlgebra SU7MotherGaugeTheory TemporalGauge
open StageNineCanonicalCauchyState
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open StageNineFormNativeP286GaugeYangMillsReadout
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

abbrev reference (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :=
  ChargedGauss.replaceMatter Stage10.Runtime.configuration matter dual
abbrev primitiveMatter (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :=
  ChargedGauss.replaceMatter (primitive potential) matter dual

theorem matter_derivative (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) (d : LorentzianIndex) :
    holonomicMatterCovariantDerivative (primitiveMatter potential matter dual) point d =
      holonomicMatterCovariantDerivative (reference matter dual) point d +
        if d = 0 then diracExteriorMotherLieAction (p286LieBlockEmbed (potential point)) (matter point) else 0 := by
  simp only [holonomicMatterCovariantDerivative, primitiveMatter, reference, ChargedGauss.replaceMatter,
    primitive, p286LieBlockEmbed_add, diracExteriorMotherLieAction_add, LinearMap.add_apply]
  split_ifs
  · module
  · simp [p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix]

private theorem kinetic_operator (source : SmoothUnifiedSource)
    (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (derivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField (primitiveMatter potential matter dual) point) derivative =
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField (reference matter dual) point) derivative := by
  simp only [matterCovariantDerivativeVariationVector, matterCovariantDerivativeKineticSum,
    toContinuumPointField, primitiveMatter, reference, ChargedGauss.replaceMatter, primitive]

theorem kinetic_increment (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedContinuumMatterKineticVector Stage10.Runtime.source 0 point
      (toContinuumPointField (primitiveMatter potential matter dual) point) =
    generatedContinuumMatterKineticVector Stage10.Runtime.source 0 point
      (toContinuumPointField (reference matter dual) point) +
      ((lapse⁻¹ : ℝ) : ℂ) • Stage9DEF.Compatibility.currentAction 0 (potential point) (matter point) := by
  have derivative : holonomicMatterCovariantDerivative (primitiveMatter potential matter dual) point =
      holonomicMatterCovariantDerivative (reference matter dual) point +
        (fun direction => if direction = 0 then
          diracExteriorMotherLieAction (p286LieBlockEmbed (potential point)) (matter point) else 0) :=
    funext (matter_derivative potential matter dual point)
  rw [Stage10.Runtime.source_eq]
  unfold generatedContinuumMatterKineticVector
  change matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
    (toContinuumPointField (primitiveMatter potential matter dual) point)
    (holonomicMatterCovariantDerivative (primitiveMatter potential matter dual) point) = _
  rw [kinetic_operator, derivative, matterCovariantDerivativeVariationVector_add]
  apply congrArg (fun vector => matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
    (toContinuumPointField (reference matter dual) point)
    (holonomicMatterCovariantDerivative (reference matter dual) point) + vector)
  unfold matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField,
    reference, ChargedGauss.replaceMatter, Stage10.Runtime.configuration_eq, actual_coframe]
  simp [Fin.sum_univ_four, homogeneousInverseGamma lapse lapse_pos.ne',
    coframeDiracMatrixMatterAction_smul_matrix, Stage9DEF.Compatibility.currentAction,
    smul_smul, mul_comm]

theorem kinetic_density_shift (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedDensitizedContinuumMatterKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitiveMatter potential matter dual) point) =
    generatedDensitizedContinuumMatterKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (reference matter dual) point) +
      (dual point (Stage9DEF.Compatibility.currentAction 0 (potential point) (matter point))).re := by
  have increment := kinetic_increment potential matter dual point
  rw [Stage10.Runtime.source_eq] at increment ⊢
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [increment]
  simp only [generatedVolumeDensity, toContinuumPointField, primitiveMatter, reference,
    ChargedGauss.replaceMatter, primitive, matterDualFrameRelative_chartZero,
    map_add, map_smul, Complex.add_re]
  rw [Stage10.Runtime.configuration_eq, actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [lapse_pos.ne']

private theorem scalar_readout (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative (formNativeP286GaugeConstitutiveReadout source background) point direction =
      holonomicScalarCovariantDerivative background point direction := rfl

theorem scalar_derivative_zero (potential : Potential) (regular : CanonicalGauss.PotentialDifferentiable potential)
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative (CanonicalGauss.configuration potential)
      (canonicalCauchySlicePoint 0 space) direction = 0 := by
  refine Fin.cases (CanonicalGauss.covariant_time_zero potential regular space) ?_ direction
  intro axis
  rw [CanonicalGauss.configuration,
    normalConstraint_scalarCovariantDerivative_spatial_zeroSlice _ _ _
      (CanonicalGauss.current_scalar_differentiable potential _)
      (CanonicalGauss.scalar_differentiable potential regular _),
    TemporalGauge.configuration, Stage10.Runtime.source_eq, scalar_readout, TemporalGauge.scalar_derivative]
  simp

private theorem kinetic_normal_readout (source readoutSource : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedDensitizedContinuumMatterKineticDensity source 0 point
      (toContinuumPointField (ChargedGauss.replaceMatter
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          (formNativeP286GaugeConstitutiveReadout readoutSource background)) matter dual) point) =
    generatedDensitizedContinuumMatterKineticDensity source 0 point
      (toContinuumPointField (ChargedGauss.replaceMatter background matter dual) point) := rfl

theorem canonical_kinetic_shift (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedDensitizedContinuumMatterKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) point) =
    generatedDensitizedContinuumMatterKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (reference matter dual) point) +
      (dual point (Stage9DEF.Compatibility.currentAction 0 (potential point) (matter point))).re := by
  rw [Stage10.Runtime.source_eq]
  unfold CanonicalGauss.withMatter CanonicalGauss.configuration TemporalGauge.configuration
  rw [Stage10.Runtime.source_eq, kinetic_normal_readout]
  have result := kinetic_density_shift potential matter dual point
  rw [Stage10.Runtime.source_eq] at result
  exact result

theorem canonical_scalar_value (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint) :
    (CanonicalGauss.withMatter potential matter dual).scalar (canonicalCauchySlicePoint 0 space) =
      Stage10.Runtime.configuration.scalar (canonicalCauchySlicePoint 0 space) := by
  change (CanonicalGauss.configuration potential).scalar _ = _
  rw [CanonicalGauss.configuration, normalConstraint_scalar_zeroSlice, CanonicalGauss.base_scalar]

theorem canonical_yukawa_preserved (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint) :
    generatedDensitizedContinuumDiracDualYukawaDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) =
    generatedDensitizedContinuumDiracDualYukawaDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (reference matter dual) (canonicalCauchySlicePoint 0 space)) := by
  rw [Stage10.Runtime.source_eq]
  unfold generatedDensitizedContinuumDiracDualYukawaDensity generatedContinuumDiracDualYukawaVector
  simp only [toContinuumPointField, canonical_scalar_value]
  rfl

private theorem scalar_withMatter (potential : Potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative (CanonicalGauss.withMatter potential matter dual) point direction =
      holonomicScalarCovariantDerivative (CanonicalGauss.configuration potential) point direction := rfl

theorem canonical_scalar_kinetic_zero (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint) :
    generatedScalarKineticDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) = 0 := by
  unfold generatedScalarKineticDensity
  simp only [toContinuumPointField, scalarFrameRelativeCovariantDerivative, Stage10.Runtime.source_eq,
    scalarFrameRelativeCoordinates_zeroChart, scalar_withMatter, scalar_derivative_zero potential regular space]
  simp [scalarCoordinatePairingRe]

private theorem reference_scalar_derivative (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative (reference matter dual) point direction =
      holonomicScalarCovariantDerivative Stage10.Runtime.configuration point direction := rfl

theorem reference_scalar_kinetic_zero (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedScalarKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (reference matter dual) point) = 0 := by
  unfold generatedScalarKineticDensity
  simp only [toContinuumPointField, scalarFrameRelativeCovariantDerivative, Stage10.Runtime.source_eq,
    scalarFrameRelativeCoordinates_zeroChart, reference_scalar_derivative,
    Stage10.Runtime.configuration_eq, actual_scalarCovariantDerivative_zero, Pi.zero_apply]
  simp [scalarCoordinatePairingRe]

theorem canonical_scalar_density_preserved (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint) :
    generatedDensitizedContinuumScalarDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) =
    generatedDensitizedContinuumScalarDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (reference matter dual) (canonicalCauchySlicePoint 0 space)) := by
  unfold generatedDensitizedContinuumScalarDensity
  rw [canonical_scalar_kinetic_zero potential regular, reference_scalar_kinetic_zero]
  simp only [toContinuumPointField, canonical_scalar_value]
  rfl

private theorem gauge_normal_matter (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField (ChargedGauss.replaceMatter
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background) matter dual) point) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField background point) := rfl

private theorem gauge_canonical (source : SmoothUnifiedSource) (potential : Potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) point) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField (TemporalGauge.configuration potential) point) :=
  gauge_normal_matter source (TemporalGauge.configuration potential) matter dual point

private theorem gauge_reference (source : SmoothUnifiedSource) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField (reference matter dual) point) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField Stage10.Runtime.configuration point) := rfl

theorem complete_static_density (potential : Potential)
    (regular : CanonicalGauss.PotentialDifferentiable potential) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) =
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField (reference matter dual) (canonicalCauchySlicePoint 0 space)) +
      lapse*squared (electric potential (canonicalCauchySlicePoint 0 space)) +
      (dual (canonicalCauchySlicePoint 0 space) (Stage9DEF.Compatibility.currentAction 0
        (potential (canonicalCauchySlicePoint 0 space)) (matter (canonicalCauchySlicePoint 0 space)))).re := by
  have scalar := canonical_scalar_density_preserved potential regular matter dual space
  have kinetic := canonical_kinetic_shift potential matter dual (canonicalCauchySlicePoint 0 space)
  have yukawa := canonical_yukawa_preserved potential matter dual space
  have gauge := gauge_density potential (canonicalCauchySlicePoint 0 space)
  have original := TemporalGauge.original_gauge_density (canonicalCauchySlicePoint 0 space)
  rw [Stage10.Runtime.source_eq] at scalar kinetic yukawa gauge original ⊢
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [scalar, kinetic, yukawa, gauge_canonical, gauge_reference, gauge, original]
  have gravity : generatedFormNativeGravityBFDensity
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) =
    generatedFormNativeGravityBFDensity
      (toContinuumPointField (reference matter dual) (canonicalCauchySlicePoint 0 space)) := rfl
  have constraint : generatedFormNativeGravityConstraintDensity
      (toContinuumPointField (CanonicalGauss.withMatter potential matter dual) (canonicalCauchySlicePoint 0 space)) =
    generatedFormNativeGravityConstraintDensity
      (toContinuumPointField (reference matter dual) (canonicalCauchySlicePoint 0 space)) := rfl
  rw [gravity, constraint]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
