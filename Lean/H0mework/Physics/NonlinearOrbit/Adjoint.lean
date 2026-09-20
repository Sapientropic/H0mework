import H0mework.Physics.NonlinearOrbit.Dirac

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineLorentzConnectionVariationDensity StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariationDensity
open StageNineMatterPointwiseEquation StageNineDiracDualYukawaSpinJurisdiction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineDynamicBreakingVacuum

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

private theorem frame (flow : LocalOrbit initial initialTime) :
    flow.configuration.coframe = fun _ => homogeneousCoframe lapse := by
  change Runtime.configuration.coframe = _
  rw [Runtime.configuration_eq, actual_coframe]

private theorem algebraicKinetic (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (variation : MatterCoordinateCarrier) (direction : LorentzianIndex) :
    flow.configuration.conjugateMatter point (Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } direction)
      (holonomicMatterVariationAlgebraicDirection flow.configuration variation point direction)) =
      if direction = 0 then 0 else (-((spinScale-flow.amplitude (point 0) : ℝ) : ℂ)/2) *
        spinPairDual ((spinScale : ℂ)*unitPhase (-flow.angle (point 0)))
          ((spinScale : ℂ)*unitPhase (flow.angle (point 0))) (matterCoordinateEquiv.symm variation) := by
  have gravity : flow.configuration.gravityConnection = fun _ => homogeneousConnection spinScale := by
    change Runtime.configuration.gravityConnection = _
    rw [Runtime.configuration_eq, actual_gravityConnection]
  unfold holonomicMatterVariationAlgebraicDirection
  rw [frame, gravity,
    show flow.configuration.gaugeConnection = fun p => gaugePotential (flow.amplitude (p 0)) from rfl,
    show flow.configuration.conjugateMatter = fun p => movingDual (flow.angle (p 0)) from rfl,
    homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
  refine Fin.cases ?_ (fun axis => ?_) direction
  · have timeSpin : diracSpinConnectionLift (homogeneousConnection spinScale) 0 = 0 := by
      simp only [diracSpinConnectionLift, homogeneousConnection,
        loweredLorentzConnectionCoefficient_ofBivectorOneForm]
      simp [homogeneousContorsion, Fin.sum_univ_six]
    simp [timeSpin, gaugePotential, p286LieBlockEmbed_zero,
      diracExteriorMotherLieAction_zero_matrix, diracMatrixMatterAction_zero_matrix]
  · simp only [Fin.succ_ne_zero, ite_false, one_smul]
    have gauge : gaugePotential (flow.amplitude (point 0)) axis.succ =
        flow.amplitude (point 0) • sourceColorP286Generator axis := by fin_cases axis <;> rfl
    rw [gauge]
    exact spinPairDual_spatialKinetic spinScale _ axis _ _ _

theorem LocalOrbit.matterAlgebraic (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (variation : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration variation point =
      -(3*lapse/2*(spinScale-flow.amplitude (point 0))) *
        (spinPairDual ((spinScale : ℂ)*unitPhase (-flow.angle (point 0)))
          ((spinScale : ℂ)*unitPhase (flow.angle (point 0))) (matterCoordinateEquiv.symm variation)).re := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField, map_add]
  have yukawa : flow.configuration.conjugateMatter point
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (flow.configuration.scalar point))
        (matterCoordinateEquiv.symm variation)) = 0 := spinPairDual_yukawa_annihilates _ _ _ _
  rw [yukawa, add_zero, Finset.smul_sum, map_sum]
  simp_rw [algebraicKinetic]
  change |(flow.configuration.coframe point).det| * _ = _
  rw [frame, homogeneousCoframe_det, abs_of_pos lapse_pos]
  simp [Fin.sum_univ_four, Complex.mul_re]
  ring

private theorem realDual_derivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (direction : LorentzianIndex) (variation : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative (fun p => lapse*(flow.configuration.conjugateMatter p variation).re) point direction =
      lapse*(if direction = 0 then temporalDual (3*lapse/2*(spinScale-flow.amplitude (point 0)))
        (flow.angle (point 0)) variation else 0).re := by
  have moving := movingDual_hasDerivAt flow.angle (point 0) _ (flow.angle_derivative _ inside) variation
  have real := (lapse • Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (point 0) moving
  have composed := real.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun p : BasePoint => lapse*(flow.configuration.conjugateMatter p variation).re) _ point at composed
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  change (coordinateDirection direction) 0 *
    (lapse*(temporalDual (3*lapse/2*(spinScale-flow.amplitude (point 0))) (flow.angle (point 0)) variation).re) = _
  by_cases same : direction = 0
  · simp [same, coordinateDirection]
  · simp [same, Ne.symm same, coordinateDirection]

theorem LocalOrbit.matterMomentum_derivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (variation : MatterCoordinateCarrier) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (matterDifferentialMomentum positiveSmoothUnifiedSource flow.configuration variation direction)
      point direction = if direction = 0 then -(3*lapse/2*(spinScale-flow.amplitude (point 0))) *
        (spinPairDual ((spinScale : ℂ)*unitPhase (-flow.angle (point 0)))
          ((spinScale : ℂ)*unitPhase (flow.angle (point 0))) (matterCoordinateEquiv.symm variation)).re else 0 := by
  have field : matterDifferentialMomentum positiveSmoothUnifiedSource flow.configuration variation direction =
      fun p => lapse*(flow.configuration.conjugateMatter p (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := homogeneousCoframe lapse, derivative := 0 } direction)
        (matterCoordinateEquiv.symm variation))).re := by
    funext p
    unfold matterDifferentialMomentum matterDifferentialVariationVector
    simp only [toContinuumPointField, frame]
    change |(homogeneousCoframe lapse).det| * _ = _
    rw [show |(homogeneousCoframe lapse).det| = lapse by rw [homogeneousCoframe_det, abs_of_pos lapse_pos]]
  rw [field, realDual_derivative flow point inside]
  by_cases temporal : direction = 0
  · subst direction
    rw [if_pos rfl, if_pos rfl, homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
    simp only [ite_true, coframeDiracMatrixMatterAction_smul_matrix]
    rw [smul_comm, map_smul]
    unfold temporalDual
    rw [spinPairDual_temporalKinetic]
    simp [Complex.mul_re]
    field_simp [ne_of_gt lapse_pos]
  · simp [temporal]

theorem LocalOrbit.adjointEuler_zero (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (variation : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration variation point = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient matterDifferentialMomentumDivergence
  rw [flow.matterAlgebraic]
  simp only [flow.matterMomentum_derivative point inside]
  simp

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
