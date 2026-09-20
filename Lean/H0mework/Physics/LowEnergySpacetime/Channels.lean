import H0mework.Physics.LowEnergySpacetime.ScalarField
import H0mework.Physics.SpinPair.Acceptance

/-! Seven original channels remain exactly zero on an arbitrary spatial radial profile. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeMatterVariation StageNineMatterPointwiseEquation
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineDiracKineticLocalSpinDensity StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineTopologicalP286GaugeThreeFormDuality StageNineFormNativeP286GaugeGeometricFirstVariation
open DiracExteriorMatterAction SU7MotherLieAlgebra SU7MotherGaugeTheory Response.Radial
noncomputable section

private theorem scalar_write_constraints (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) (scalar : BasePoint → ScalarCoordinateCarrier) (point : BasePoint) :
    let original := diracDualFormNativePointwiseJointResidual source current point
    let modified := diracDualFormNativePointwiseJointResidual source {current with scalar := scalar} point
    modified.gravityMultiplier = original.gravityMultiplier ∧
    modified.gravityAuxiliary = original.gravityAuxiliary ∧
    modified.p286GaugeAuxiliary = original.p286GaugeAuxiliary ∧
    modified.lorentzConnection = original.lorentzConnection :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem four_constraints (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint) :
    let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (configuration profile parameter) point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 := by
  have baseline := (diracDualFormNativeJointZeroFiber_iff_pointwise _ _).mp actual_jointZeroFiber point
  have same := scalar_write_constraints positiveSmoothUnifiedSource actual
    (fun p => direction+(parameter*profile p) • direction) point
  change diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource actual point = 0 at baseline
  exact ⟨same.1.trans (congrArg (·.gravityMultiplier) baseline),
    same.2.1.trans (congrArg (·.gravityAuxiliary) baseline),
    same.2.2.1.trans (congrArg (·.p286GaugeAuxiliary) baseline),
    same.2.2.2.trans (congrArg (·.lorentzConnection) baseline)⟩

theorem kinetic_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point) = 0 :=
  actual_kineticVector_zero point

theorem yukawa_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point) = 0 := by
  unfold generatedContinuumDiracDualYukawaVector
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm (direction+(parameter*profile point) • direction)) (actual.matter point) = 0
  rw [actual_matter]
  exact Evolution.radialYukawa_zero _ _ _

theorem primal_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (test : MatterCoordinateCarrier) :
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point = 0 := by
  unfold diracDualConjugateMatterDirectionalCoefficient generatedContinuumDiracDualMatterVector
  rw [kinetic_zero, yukawa_zero]
  simp

theorem adjoint_algebraic_same (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (test : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point =
      diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource actual test point := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
  change |(actual.coframe point).det| * (actual.conjugateMatter point (_+_)).re =
    |(actual.coframe point).det| * (actual.conjugateMatter point (_+_)).re
  rw [actual_conjugateMatter, map_add, map_add, spinPairDual_yukawa_annihilates,
    spinPairDual_yukawa_annihilates, add_zero, add_zero]
  rfl

theorem adjoint_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (test : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [adjoint_algebraic_same]
  change diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource actual test point-
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource actual test point = 0
  exact actual_matterEuler_zero point test

theorem scalar_current_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (variation : P286GaugeOneForm) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point)
      (pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField (configuration profile parameter) point) variation) = 0 := by
  rw [kinetic_first profile parameter point differentiable]
  have cross (mu : LorentzianIndex) :
      scalarCoordinatePairingRe
        (pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField (configuration profile parameter) point) variation mu) direction = 0 := by
    change scalarCoordinatePairingRe
      (scalarMotherLieAction _ (direction+(parameter*profile point) • direction)) direction = 0
    rw [scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
      scalarCoordinatePairingRe_add_left, scalarCoordinatePairingRe_real_smul_left,
      radial_gauge_cross_zero, mul_zero, add_zero]
  simp only [cross, mul_zero, Finset.sum_const_zero]

theorem charged_coefficient_same (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (variation : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point) variation =
      formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
        (toContinuumPointField actual point) variation := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [scalar_current_zero profile parameter point differentiable,
    actual_scalarKineticFirstVariation_zero, zero_add, zero_add]
  rfl

theorem charged_three_form_same (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point (toContinuumPointField actual point) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro variation
  exact charged_coefficient_same profile parameter point differentiable variation

theorem gauge_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
      (configuration profile parameter) point = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [charged_three_form_same profile parameter point differentiable]
  exact actual_gaugeEuler_zero point

theorem seven_channels_zero (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) :
    let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (configuration profile parameter) point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 ∧
      residual.p286GaugeConnection = 0 ∧ residual.matter = 0 ∧ residual.conjugateMatter = 0 := by
  obtain ⟨multiplier,gravityAuxiliary,gaugeAuxiliary,lorentz⟩ := four_constraints profile parameter point
  exact ⟨multiplier,gravityAuxiliary,gaugeAuxiliary,lorentz,
    gauge_zero profile parameter point differentiable,
    funext (adjoint_zero profile parameter point), funext (primal_zero profile parameter point)⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
