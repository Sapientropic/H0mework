import H0mework.Versions.AB.Physics.MotherSource.HyperchargeResponse.Scalar

/-! Complete temporal gauge response, retaining the original independent dual. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
namespace SaturationMonoid.PhysicsCore.Stage10.HyperchargeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualYukawaLocalSpinDensity
open StageNineP286GaugeConnectionActionVariation StageNineScalarLocalSpinDensity
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift StageNineCoframeSpinRepresentation
open StageNineMatterVariation StageNineCoframeLocalDifferentiability
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeMotherAction
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def matterCharge (point : BasePoint) : DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed chargeDirection)
    (Stage10.Runtime.configuration.matter point)

theorem matter_derivative (potential : BasePoint → ℝ) (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative (primitive potential) point direction =
      holonomicMatterCovariantDerivative Stage10.Runtime.configuration point direction +
        if direction = 0 then (potential point : ℂ) • matterCharge point else 0 := by
  simp only [holonomicMatterCovariantDerivative, primitive, p286LieBlockEmbed_add,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_add,
    diracExteriorMotherLieAction_real_smul, LinearMap.add_apply, LinearMap.smul_apply,
    matterCharge]
  split_ifs
  · module
  · simp only [Complex.ofReal_zero, zero_smul, add_zero]

theorem temporal_dual_zero (point : BasePoint) :
    Stage10.Runtime.configuration.conjugateMatter point
      (Complex.I • diracMatrixMatterAction (diracGamma 0) (matterCharge point)) = 0 := by
  rw [matterCharge, Stage10.Runtime.configuration_eq]
  have result := Stage9DEF.Compatibility.current_classical_quantum point 0 chargeDirection
  rw [actual_spinPairCurrent_time] at result
  exact (Stage9DEF.Compatibility.actual_action_quantumResponse point
    (Stage9DEF.Compatibility.currentAction 0 chargeDirection)).trans result.symm

theorem kinetic_operator_preserved (source : SmoothUnifiedSource)
    (potential : BasePoint → ℝ) (point : BasePoint)
    (derivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField (primitive potential) point) derivative =
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField Stage10.Runtime.configuration point) derivative := by
  simp only [matterCovariantDerivativeVariationVector, matterCovariantDerivativeKineticSum,
    toContinuumPointField, primitive]

theorem kinetic_increment (potential : BasePoint → ℝ) (point : BasePoint) :
    generatedContinuumMatterKineticVector Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedContinuumMatterKineticVector Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) +
      ((potential point / lapse : ℝ) : ℂ) •
        (Complex.I • diracMatrixMatterAction (diracGamma 0) (matterCharge point)) := by
  have derivative : holonomicMatterCovariantDerivative (primitive potential) point =
      holonomicMatterCovariantDerivative Stage10.Runtime.configuration point +
        (fun direction => if direction = 0 then (potential point : ℂ) • matterCharge point else 0) :=
    funext (matter_derivative potential point)
  rw [Stage10.Runtime.source_eq]
  unfold generatedContinuumMatterKineticVector
  change matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
    (toContinuumPointField (primitive potential) point)
    (holonomicMatterCovariantDerivative (primitive potential) point) = _
  rw [kinetic_operator_preserved]
  rw [derivative]
  rw [matterCovariantDerivativeVariationVector_add]
  apply congrArg (fun vector =>
    matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField Stage10.Runtime.configuration point)
      (holonomicMatterCovariantDerivative Stage10.Runtime.configuration point) + vector)
  unfold matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField,
    Stage10.Runtime.configuration_eq, actual_coframe]
  simp [Fin.sum_univ_four, homogeneousInverseGamma lapse (ne_of_gt lapse_pos),
    coframeDiracMatrixMatterAction_smul_matrix, smul_smul, div_eq_mul_inv]
  congr 1
  ring

theorem dirac_density_preserved (potential : BasePoint → ℝ) (point : BasePoint) :
    generatedDensitizedContinuumDiracDualMatterDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedDensitizedContinuumDiracDualMatterDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) := by
  have increment := kinetic_increment potential point
  rw [Stage10.Runtime.source_eq] at increment ⊢
  unfold generatedDensitizedContinuumDiracDualMatterDensity
  have yukawa : generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) := by
    simp only [generatedDensitizedContinuumDiracDualYukawaDensity,
      generatedContinuumDiracDualYukawaVector, generatedVolumeDensity,
      toContinuumPointField, primitive]
  rw [yukawa]
  apply congrArg (fun value => value +
    generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField Stage10.Runtime.configuration point))
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [increment]
  simp only [generatedVolumeDensity, toContinuumPointField, primitive,
    matterDualFrameRelative_chartZero]
  rw [map_add, map_smul, temporal_dual_zero, smul_zero, add_zero]

theorem scalar_density_shift (potential : BasePoint → ℝ) (point : BasePoint) :
    generatedDensitizedContinuumScalarDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      generatedDensitizedContinuumScalarDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) - (potential point)^2 / lapse := by
  have kinetic := actual_scalar_kinetic_exact potential point
  rw [Stage10.Runtime.source_eq] at kinetic ⊢
  have original : generatedScalarKineticDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField Stage10.Runtime.configuration point) = 0 := by
    rw [Stage10.Runtime.configuration_eq]
    simp [generatedScalarKineticDensity, toContinuumPointField,
      actual_scalarCovariantDerivative_zero, scalarFrameRelativeCovariantDerivative,
      scalarCoordinatePairingRe]
  unfold generatedDensitizedContinuumScalarDensity
  rw [kinetic, original]
  simp only [generatedVolumeDensity, toContinuumPointField, primitive]
  rw [Stage10.Runtime.configuration_eq, actual_coframe, homogeneousCoframe_det,
    abs_of_pos lapse_pos]
  field_simp [ne_of_gt lapse_pos]
  ring

theorem constitutive_matter_preserved (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    generatedDiracDualFormNativeMatterDensity source 0 point
      (toContinuumPointField (formNativeP286GaugeConstitutiveReadout source background) point) =
      generatedDiracDualFormNativeMatterDensity source 0 point
        (toContinuumPointField background point) := rfl

theorem primitive_zero : primitive (fun _ => 0) = Stage10.Runtime.configuration := by
  apply StageNineHolonomicConfiguration.ext <;>
    simp only [primitive, ite_self, zero_smul, add_zero]

theorem configuration_zero : configuration (fun _ => 0) = Stage10.Runtime.configuration := by
  unfold configuration
  rw [primitive_zero, Stage10.Runtime.source_eq, Stage10.Runtime.configuration_eq]
  symm
  apply (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
    positiveSmoothUnifiedSource actual actual_nondegenerate).mp
  intro point
  exact (Stage9G.Foundation.actualConstitutive_solves point).symm

theorem original_gauge_density (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings Stage10.Runtime.source)
      (toContinuumPointField Stage10.Runtime.configuration point) = magneticDensity := by
  have zero := actual_gauge_density (fun _ => 0) point (differentiableAt_const _)
  rw [configuration_zero] at zero
  simpa [fieldDirectionalDerivative] using zero

/-- Full original mother density, with no scalar/Dirac term discarded. -/
theorem mother_density_shift (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (configuration potential) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) +
      stiffness / 2 * (∑ axis : Fin 3,
        (fieldDirectionalDerivative potential point axis.succ)^2) -
      (potential point)^2 / lapse := by
  have matter : generatedDiracDualFormNativeMatterDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (configuration potential) point) =
      generatedDiracDualFormNativeMatterDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) - (potential point)^2 / lapse := by
    have scalarShift := scalar_density_shift potential point
    have diracShift := dirac_density_preserved potential point
    rw [Stage10.Runtime.source_eq] at scalarShift diracShift ⊢
    simp only [configuration, Stage10.Runtime.source_eq]
    rw [constitutive_matter_preserved]
    unfold generatedDiracDualFormNativeMatterDensity
    rw [scalarShift, diracShift]
    ring
  have gravity : generatedFormNativeGravityBFDensity
      (toContinuumPointField (configuration potential) point) =
      generatedFormNativeGravityBFDensity
        (toContinuumPointField Stage10.Runtime.configuration point) := by
    simp only [generatedFormNativeGravityBFDensity, toContinuumPointField,
      configuration, formNativeP286GaugeConstitutiveReadout, primitive]
    rfl
  have constraint : generatedFormNativeGravityConstraintDensity
      (toContinuumPointField (configuration potential) point) =
      generatedFormNativeGravityConstraintDensity
        (toContinuumPointField Stage10.Runtime.configuration point) := by
    simp only [generatedFormNativeGravityConstraintDensity,
      generatedGravitySimplicityResidual, toContinuumPointField,
      configuration, formNativeP286GaugeConstitutiveReadout, primitive]
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [gravity, constraint, actual_gauge_density potential point regular,
    original_gauge_density, matter]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.HyperchargeResponse
