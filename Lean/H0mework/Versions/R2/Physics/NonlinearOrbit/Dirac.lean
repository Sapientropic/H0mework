import H0mework.Versions.R2.Physics.NonlinearOrbit.GaugeEquation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction StageNineP286GaugeConnectionVariationDensity
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

theorem LocalOrbit.yukawaVector_zero (flow : LocalOrbit initial initialTime) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) = 0 := by
  unfold generatedContinuumDiracDualYukawaVector
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm (scalarFrameRelativeCoordinates positiveSmoothUnifiedSource 0 point
      (flow.configuration.scalar point)))
    (matterFrameRelative positiveSmoothUnifiedSource 0 point (flow.configuration.matter point)) = 0
  have scalar : flow.configuration.scalar = fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    change Runtime.configuration.scalar = _
    rw [Runtime.configuration_eq, actual_scalar]
  rw [scalar, scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply]
  unfold diracDualRightChiralYukawaAction
  rw [LinearMap.comp_apply]
  change (fun spin => exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (∑ other, rightChiralityProjector spin other •
      sourceColorDiracMatter (spinPairCoefficients (unitPhase (flow.angle (point 0)))
        (unitPhase (-flow.angle (point 0)))) other)) = 0
  funext spin
  simp only [sourceColorDiracMatter, map_sum, map_smul,
    sourceColorDoublet_internalYukawa_zero, smul_zero, Finset.sum_const_zero]
  rfl

theorem LocalOrbit.primalEuler_zero (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) = 0 := by
  unfold generatedContinuumDiracDualMatterVector
  rw [flow.primalKinetic_zero point inside, flow.yukawaVector_zero, add_zero]

theorem LocalOrbit.dualDerivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (direction : LorentzianIndex) (variation : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative (fun candidate => flow.configuration.conjugateMatter candidate variation) point direction =
      if direction = 0 then
        temporalDual (3*lapse/2*(spinScale-flow.amplitude (point 0))) (flow.angle (point 0)) variation else 0 := by
  have derivative := movingDual_hasDerivAt flow.angle (point 0) _ (flow.angle_derivative _ inside) variation
  have composed := derivative.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun candidate : BasePoint => flow.configuration.conjugateMatter candidate variation) _ point at composed
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  change (coordinateDirection direction) 0 •
    temporalDual (3*lapse/2*(spinScale-flow.amplitude (point 0))) (flow.angle (point 0)) variation = _
  by_cases same : direction = 0
  · simp [same, coordinateDirection]
  · simp [same, Ne.symm same, coordinateDirection]

theorem LocalOrbit.adjointJet_zero (flow : LocalOrbit initial initialTime) (time : ℝ)
    (inside : time ∈ flow.window) (variation : DiracExteriorMatterCarrier) :
    adjointJet (flow.amplitude time) (deriv flow.angle time) (flow.angle time) variation = 0 := by
  rw [adjointJet_eq, (flow.angle_derivative time inside).deriv]
  have coefficient : (((3*lapse/2*(spinScale-flow.amplitude time) : ℝ) : ℂ)/(lapse : ℂ)) -
      3*((spinScale-flow.amplitude time : ℝ) : ℂ)/2 = 0 := by
    push_cast
    field_simp [show (lapse : ℂ) ≠ 0 by exact_mod_cast ne_of_gt lapse_pos]
    ring
  rw [coefficient, zero_mul]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
