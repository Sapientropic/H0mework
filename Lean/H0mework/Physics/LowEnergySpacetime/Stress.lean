import H0mework.Physics.LowEnergySpacetime.ScalarField
import H0mework.Physics.LowEnergyContact.Stress

/-! Full original coframe feedback of a spatial radial field is quadratic in amplitude. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineCoframeVariation Stage9C.Dynamics.Homogeneous
open StageNineScalarLocalSpinDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineDiracDualYukawaLocalSpinDensity
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open Response.Radial
open scoped Topology Matrix.Norms.Elementwise
noncomputable section

private theorem radial_pair (first second : ℝ) :
    scalarCoordinatePairingRe (first • direction) (second • direction) =
      first*second*Contact.Stress.weight := by
  rw [scalarCoordinatePairingRe_real_smul_left, scalarCoordinatePairingRe_real_smul_right]
  have self : scalarCoordinatePairingRe direction direction = Contact.Stress.weight :=
    scalarCoordinateRealPairing_self direction
  rw [self]
  ring

private theorem radial_norm (amplitude : ℝ) :
    scalarCoordinateSquaredNorm (amplitude • direction) = amplitude^2*Contact.Stress.weight := by
  rw [← scalarCoordinateRealPairing_self]
  change scalarCoordinatePairingRe (amplitude • direction) (amplitude • direction) = _
  rw [radial_pair]
  ring

theorem scalar_frozen_density (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField (configuration profile parameter) point) candidate) =
      parameter^2 * |candidate.det| * Contact.Stress.weight *
        ((1/2:ℝ)*(∑ mu, ∑ nu, (lorentzianMetricOfCoframe candidate)⁻¹ mu nu*
          coordinateDerivative profile mu point*coordinateDerivative profile nu point)-(profile point)^2) := by
  have derivative := funext (scalar_covariant profile parameter point differentiable)
  unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity generatedScalarPotential
  simp only [generatedVolumeDensity, withCoframe, toContinuumPointField,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart, derivative]
  change _ * ((1/2:ℝ)*(∑ mu, ∑ nu, (lorentzianMetricOfCoframe candidate)⁻¹ mu nu*
    scalarCoordinatePairingRe ((parameter*coordinateDerivative profile mu point) • direction)
      ((parameter*coordinateDerivative profile nu point) • direction))-
      scalarCoordinateSquaredNorm (direction+(parameter*profile point) • direction-direction)) = _
  rw [add_sub_cancel_left, radial_norm]
  simp only [radial_pair, Fin.sum_univ_four]
  ring

private theorem point_field (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) :
    toContinuumPointField (configuration profile parameter) point =
      { toContinuumPointField actual point with
        scalar := direction+(parameter*profile point) • direction
        scalarCovariantDerivative := fun mu => (parameter*coordinateDerivative profile mu point) • direction } := by
  have derivative := funext (scalar_covariant profile parameter point differentiable)
  change { toContinuumPointField actual point with
    scalar := direction+(parameter*profile point) • direction
    scalarCovariantDerivative := holonomicScalarCovariantDerivative (configuration profile parameter) point } = _
  rw [derivative]

private theorem yukawa_density (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField (configuration profile parameter) point) candidate) = 0 := by
  unfold generatedDensitizedContinuumDiracDualYukawaDensity generatedContinuumDiracDualYukawaVector
  simp only [matterDualFrameRelative_zeroChart, matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart, withCoframe, toContinuumPointField]
  change _*((actual.conjugateMatter point) _).re = 0
  rw [actual_conjugateMatter, spinPairDual_yukawa_annihilates]
  simp

theorem coframe_density_quadratic (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (candidate : LorentzianCoframe) :
    diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource point
      (toContinuumPointField (configuration profile parameter) point) candidate =
      diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource point
        (toContinuumPointField actual point) candidate+
      parameter^2*(diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource point
        (toContinuumPointField (configuration profile 1) point) candidate-
        diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource point
          (toContinuumPointField actual point) candidate) := by
  have baseline : generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField actual point) candidate) = 0 := by
    simp [generatedDensitizedContinuumScalarDensity, generatedScalarKineticDensity,
      generatedScalarPotential, toContinuumPointField, withCoframe,
      actual_scalarCovariantDerivative_zero, actual_scalar,
      scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]
  have originalYukawa : generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField actual point) candidate) = 0 := by
    simpa only [configuration_zero] using yukawa_density profile 0 point candidate
  simp only [diracDualFormNativeCoframeLocalDensity,
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity,
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary,
    generatedDiracDualFormNativeMatterDensity, generatedDensitizedContinuumDiracDualMatterDensity]
  rw [scalar_frozen_density profile parameter point differentiable,
    scalar_frozen_density profile 1 point differentiable, baseline,
    yukawa_density, yukawa_density, originalYukawa]
  rw [point_field profile parameter point differentiable, point_field profile 1 point differentiable]
  let original := withCoframe (toContinuumPointField actual point) candidate
  let invariant := StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity original+
    StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity original+
    StageNineFormNativeMotherAction.generatedFormNativeGaugeDensityAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) original
  let kinetic := StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
    positiveSmoothUnifiedSource 0 point original
  let energy := (1/2:ℝ)*(∑ mu, ∑ nu, (lorentzianMetricOfCoframe candidate)⁻¹ mu nu*
    coordinateDerivative profile mu point*coordinateDerivative profile nu point)-(profile point)^2
  change invariant+(parameter^2 * |candidate.det| * Contact.Stress.weight*energy+(kinetic+0)) =
    invariant+(0+(kinetic+0))+parameter^2*
      (invariant+((1:ℝ)^2 * |candidate.det| * Contact.Stress.weight*energy+(kinetic+0))-
        (invariant+(0+(kinetic+0))))
  ring

theorem coframe_euler_quadratic (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField (configuration profile parameter) point) variation =
      parameter^2*diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
        (toContinuumPointField (configuration profile 1) point) variation := by
  have baseline := diracDualFormNativeCoframeLocalDensity_path_hasDerivAt
    positiveSmoothUnifiedSource point (toContinuumPointField actual point)
    (actual_nondegenerate point) variation
  have unit := diracDualFormNativeCoframeLocalDensity_path_hasDerivAt
    positiveSmoothUnifiedSource point (toContinuumPointField (configuration profile 1) point)
    (actual_nondegenerate point) variation
  have evaluated := diracDualFormNativeCoframeLocalDensity_path_hasDerivAt
    positiveSmoothUnifiedSource point (toContinuumPointField (configuration profile parameter) point)
    (actual_nondegenerate point) variation
  have computed := baseline.add ((unit.sub baseline).const_mul (parameter^2))
  have same := computed.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => coframe_density_quadratic profile parameter point differentiable
      ((actual.coframe point)+t • variation)))
  have equal := evaluated.unique same
  simpa only [actual_coframeEuler_zero, zero_apply, sub_zero, zero_add] using equal

theorem coframe_first_zero (profile : BasePoint → ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (variation : LorentzianCoframe) :
    HasDerivAt (fun parameter => diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField (configuration profile parameter) point) variation) 0 0 := by
  rw [funext (fun parameter => coframe_euler_quadratic profile parameter point differentiable variation)]
  convert! ((hasDerivAt_id (x := (0:ℝ))).pow 2).mul_const
    (diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField (configuration profile 1) point) variation) using 1
  norm_num

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
