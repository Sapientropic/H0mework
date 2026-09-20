import H0mework.Physics.NonlinearOrbit.Configuration

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineDynamicBreakingVacuum SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction
open StageNineP286GaugeConnectionVariation

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

theorem LocalOrbit.scalarDerivative_zero (flow : LocalOrbit initial initialTime) (point : BasePoint) :
    holonomicScalarCovariantDerivative flow.configuration point = 0 := by
  have scalar : flow.configuration.scalar = fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    change Runtime.configuration.scalar = _
    rw [Runtime.configuration_eq, actual_scalar]
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [scalar]
  unfold fieldDirectionalDerivative
  rw [(hasFDerivAt_const (𝕜 := ℝ) (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) point).fderiv]
  simp only [zero_apply, zero_add]
  rw [show flow.configuration.gaugeConnection = fun p => gaugePotential (flow.amplitude (p 0)) from rfl]
  fin_cases direction
  · simp [gaugePotential, p286LieBlockEmbed_zero, scalarMotherLieAction]
  all_goals simp [gaugePotential, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_real_smul, sourceColorP286Generator_vacuum_zero]

theorem LocalOrbit.scalarFirst_zero (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) variation = 0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  change (1/2:ℝ) * ∑ first, ∑ second,
    ((lorentzianMetricOfCoframe (flow.configuration.coframe point))⁻¹ first second) *
      (scalarCoordinatePairingRe
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point variation first)
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point
          (holonomicScalarCovariantDerivative flow.configuration point) second) +
       scalarCoordinatePairingRe
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point
          (holonomicScalarCovariantDerivative flow.configuration point) first)
        (scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0 point variation second)) = 0
  rw [flow.scalarDerivative_zero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
