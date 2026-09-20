import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.GaugeAction.P286GaugeYangMillsReadout
import H0mework.Physics.SpinPair.Actual

/-! The fixed source coframe generates a flat, torsion-free pullback of the
Dirac-dual mother action with arbitrary P286 connection. The constitutive
inverse supplies the auxiliary field; the charged Euler term is proved zero.
The discarded scalar potential is an explicit connection-independent density.
This restriction does not impose the discarded gravitational equations. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Flat

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionActionVariation
open StageNineDynamicBreakingVacuum StageNineScalarLocalSpinDensity
open StageNineFormNativeMotherAction StageNineDiracDualFormNativeMotherAction
open StageNineFormNativeGaugeWedge StageNineFormNativeGaugeAuxiliaryVariation
open StageNineTopologicalGravityCurvatureVariancePairing
open StageNineCoframeFirstJet StageNineCartanAffineConnectionActualization
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

def coframe : LorentzianCoframe := Stage9C.Material.SpinPair.actual.coframe 0

def primitive (connection : P286ConnectionField) : StageNineHolonomicConfiguration where
  coframe := fun _ => coframe
  gravityConnection := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection := connection
  gaugeAuxiliary := 0
  scalar := 0
  matter := 0
  conjugateMatter := 0

def configuration (connection : P286ConnectionField) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource (primitive connection)

theorem nondegenerate (connection : P286ConnectionField) :
    (configuration connection).Nondegenerate :=
  fun _ => Stage9C.Material.SpinPair.actual_nondegenerate 0

theorem auxiliary_equation (connection : P286ConnectionField) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation positiveSmoothUnifiedSource
      (configuration connection) :=
  formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation _ _
    (fun _ => Stage9C.Material.SpinPair.actual_nondegenerate 0)

@[simp] theorem connection_preserved (connection : P286ConnectionField) :
    (configuration connection).gaugeConnection = connection := rfl

theorem curvature_preserved (connection : P286ConnectionField) (point : BasePoint) :
    holonomicGaugeCurvature (configuration connection) point =
      holonomicGaugeCurvature (primitive connection) point := rfl

theorem gravity_curvature_zero (connection : P286ConnectionField) (point : BasePoint) :
    holonomicGravityCurvature (configuration connection) point = 0 := by
  funext internalPair spacetimePair
  simp [holonomicGravityCurvature, gravityConnectionDerivative, configuration,
    formNativeP286GaugeConstitutiveReadout, primitive]

theorem torsion_zero (connection : P286ConnectionField) (point : BasePoint) :
    actualPointwiseCartanTorsionTwoForm
      (holonomicCoframeFirstJetAt (configuration connection).coframe point)
      ((configuration connection).gravityConnection point) = 0 := by
  ext pair internal
  simp [actualPointwiseCartanTorsionTwoForm, pointwiseCartanTorsion,
    pointwiseCoframeCovariantDerivative, coframeConnectionAction, holonomicCoframeFirstJetAt,
    configuration, formNativeP286GaugeConstitutiveReadout, primitive]

theorem charged_coefficient_zero (connection : P286ConnectionField)
    (point : BasePoint) (direction : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration connection) point) direction = 0 := by
  simp [formNativeChargedGaugeFirstCoefficient,
    scalarGaugeConnectionKineticFirstVariationDensity,
    pointwiseScalarP286GaugeConnectionVariation,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates,
    scalarCoordinatePairingRe, matterGaugeConnectionFirstVariationDensity,
    matterDualFrameRelative, toContinuumPointField, configuration,
    formNativeP286GaugeConstitutiveReadout, primitive]

theorem charged_current_zero (connection : P286ConnectionField) (point : BasePoint) :
    formNativePhysicalChargedGaugeCurrentThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration connection) point) = 0 := by
  unfold formNativePhysicalChargedGaugeCurrentThreeForm
  rw [(formNativeChargedGaugeThreeForm_eq_zero_iff_all _ _ _ _).2
    (charged_coefficient_zero connection point), neg_zero]

def density (connection : P286ConnectionField) (point : BasePoint) : ℝ :=
  (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient
    ((configuration connection).gaugeAuxiliary point)
    (holonomicGaugeCurvature (configuration connection) point)

theorem gauge_density (connection : P286ConnectionField) (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField (configuration connection) point) = density connection point := by
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  have equation := auxiliary_equation connection point
  unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary at equation
  rw [← equation]
  dsimp only [toContinuumPointField, density]
  ring

theorem scalar_derivative_zero (connection : P286ConnectionField) (point : BasePoint) :
    holonomicScalarCovariantDerivative (configuration connection) point = 0 := by
  funext direction
  simp [holonomicScalarCovariantDerivative, fieldDirectionalDerivative, configuration,
    formNativeP286GaugeConstitutiveReadout, primitive]

theorem mother_density (connection : P286ConnectionField) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration connection) point) =
    density connection point - |coframe.det| *
      generatedScalarPotential positiveSmoothUnifiedSource 0 point 0 := by
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [gauge_density]
  unfold generatedDiracDualFormNativeMatterDensity
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing]
  simp only [generatedDensitizedContinuumScalarDensity, generatedScalarKineticDensity,
    toContinuumPointField, scalar_derivative_zero]
  simp [generatedFormNativeGravityBFDensity, generatedFormNativeGravityConstraintDensity,
    gravityTopologicalBFCoefficient,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates,
    scalarCoordinatePairingRe, generatedVolumeDensity, matterDualFrameRelative,
    configuration, formNativeP286GaugeConstitutiveReadout, primitive]
  ring

theorem reduced_euler (connection : P286ConnectionField) (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
      (configuration connection) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (configuration connection) point := by
  have charged := charged_current_zero connection point
  unfold formNativePhysicalChargedGaugeCurrentThreeForm at charged
  have zero := neg_eq_zero.mp charged
  simp only [holonomicFormNativeP286GaugeEulerThreeForm, zero, add_zero]

theorem gauge_equation_iff (connection : P286ConnectionField) :
    FormNativeP286GaugeConnectionPointwiseEquation positiveSmoothUnifiedSource
      (configuration connection) ↔
      ∀ point, holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (configuration connection) point = 0 := by
  simp only [FormNativeP286GaugeConnectionPointwiseEquation, charged_current_zero]

def actionOn (region : Set BasePoint) (connection : P286ConnectionField) : ℝ :=
  ∫ point in region, density connection point

theorem action_from_mother (region : Set BasePoint) (connection : P286ConnectionField) :
    (∫ point in region,
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField (configuration connection) point) +
        |coframe.det| * generatedScalarPotential positiveSmoothUnifiedSource 0 point 0) =
      actionOn region connection := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  rw [mother_density]
  ring

end
end SaturationMonoid.PhysicsCore.YangMills.Flat
