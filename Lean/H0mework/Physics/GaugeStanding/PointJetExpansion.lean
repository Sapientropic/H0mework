import H0mework.Physics.GaugeAction.P286GaugeConnectionVariation
import H0mework.Physics.GaugeStanding.MatterDensityCancellation
import H0mework.Physics.GaugeStanding.ScalarKineticCancellation

/-!
# S9-C: actual linked P286 point-jet expansion

The linked primitive path is linear only in the primitive fields.  Its
derived curvature and covariant jets are genuinely quadratic because the
connection acts on the simultaneously varied charged fields.

This module records those exact path readouts on the one actual
`p286LinkedActivePrimitivePath`.  They are the path-level input for the
local-density derivative; no Ward coefficient, stationarity law, residual
zero, or supplied jet receipt is used.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActivePointJetExpansion

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveMatterCovariantJet
open StageNineP286LinkedActiveMatterDensityCancellation
open StageNineP286LinkedActiveScalarCovariantJet
open StageNineP286LinkedActiveScalarKineticCancellation
open StageNineP286LinkedActiveVariation
open StageNineP286LinkedActiveVariationRegularity
open StageNineScalarVariation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

/-! ## Quadratic responses forced by the same primitive tangent -/

def linkedActiveP286CurvatureLinearResponse
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : P286GaugeTwoForm :=
  p286GaugeConnectionLinearCurvatureVariation configuration
    (fun current =>
      (representationDerivedP286CoupledGaugeTangentSection configuration
        gaugeParameter current).connection)
    point

def linkedActiveP286CurvatureQuadraticResponse
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : P286GaugeTwoForm :=
  p286GaugeConnectionQuadraticCurvatureVariation
    (fun current =>
      (representationDerivedP286CoupledGaugeTangentSection configuration
        gaugeParameter current).connection)
    point

def linkedActiveScalarCovariantJetQuadraticResponse
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  scalarP286ActionBilinear
    ((representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter point).connection direction)
    ((representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter point).scalar)

def linkedActiveMatterCovariantJetQuadraticResponse
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction
    (p286LieBlockEmbed
      (p286CoordinateEquiv.symm
        ((representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).connection direction)))
    ((representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter point).matter)

/-! ## Exact readouts of the one linked path -/

theorem p286LinkedActivePrimitivePath_curvatureCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ)
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        (p286LinkedActivePrimitivePath configuration gaugeParameter parameter)
        point =
      holonomicP286GaugeCurvatureCoordinate configuration point +
        parameter •
          linkedActiveP286CurvatureLinearResponse configuration gaugeParameter
            point +
        parameter ^ 2 •
          linkedActiveP286CurvatureQuadraticResponse configuration
            gaugeParameter point := by
  change
    holonomicP286GaugeCurvatureCoordinate
        (varyP286GaugeConnectionCoordinate configuration
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          parameter)
        point = _
  change
    holonomicP286GaugeCurvatureCoordinate
        (varyP286GaugeConnectionCoordinate configuration
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          parameter)
        point =
      holonomicP286GaugeCurvatureCoordinate configuration point +
        parameter •
          p286GaugeConnectionLinearCurvatureVariation configuration
            (p286InfinitesimalGaugeConnectionVariation configuration smooth
              gaugeParameter)
            point +
        parameter ^ 2 •
          p286GaugeConnectionQuadraticCurvatureVariation
            (p286InfinitesimalGaugeConnectionVariation configuration smooth
              gaugeParameter)
            point
  exact
    holonomicP286GaugeCurvatureCoordinate_expansion configuration smooth
      (p286InfinitesimalGaugeConnectionVariation configuration smooth
        gaugeParameter)
      parameter point

theorem p286LinkedActivePrimitivePath_scalarCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (p286LinkedActivePrimitivePath configuration gaugeParameter parameter)
        point direction =
      holonomicScalarCovariantDerivative configuration point direction +
        parameter •
          linkedActiveScalarCovariantJetResponse configuration gaugeParameter
            point direction +
        parameter ^ 2 •
          linkedActiveScalarCovariantJetQuadraticResponse configuration
            gaugeParameter point direction := by
  let connectionVariation :=
    p286InfinitesimalGaugeConnectionVariation configuration smooth
      gaugeParameter
  let scalarVariation :=
    p286LinkedActiveScalarVariation configuration smooth gaugeParameter
  change
    holonomicScalarCovariantDerivative
        (varyP286GaugeConnectionCoordinate
          (varyScalarCoordinates configuration scalarVariation parameter)
          connectionVariation parameter)
        point direction = _
  rw [holonomicScalarCovariantDerivative_gaugeConnection_expansion,
    holonomicScalarCovariantDerivative_varyScalarCoordinates
      configuration smooth scalarVariation parameter point direction]
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
    linkedActiveScalarCovariantJetResponse
    linkedActiveScalarCovariantJetQuadraticResponse
    holonomicScalarVariationCovariantDerivative
    connectionVariation scalarVariation
  simp only [varyScalarCoordinates,
    p286InfinitesimalGaugeConnectionVariation_apply,
    p286LinkedActiveScalarVariation_apply,
    scalarMotherLieAction_add_right,
    scalarMotherLieAction_real_smul_right]
  simp [p286LinkedActiveScalarVariation, scalarVariationCoordinateDerivative,
    scalarP286ActionBilinear, holonomicP286GaugeConnectionCoordinate]
  module

theorem p286LinkedActivePrimitivePath_matterCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (p286LinkedActivePrimitivePath configuration gaugeParameter parameter)
        point direction =
      holonomicMatterCovariantDerivative configuration point direction +
        parameter •
          linkedActiveMatterCovariantJetResponse configuration gaugeParameter
            point direction +
        parameter ^ 2 •
          linkedActiveMatterCovariantJetQuadraticResponse configuration
            gaugeParameter point direction := by
  let connectionVariation :=
    p286InfinitesimalGaugeConnectionVariation configuration smooth
      gaugeParameter
  let matterVariation :=
    p286LinkedActiveMatterVariation configuration smooth gaugeParameter
  change
    holonomicMatterCovariantDerivative
        (varyP286GaugeConnectionCoordinate
          (varyMatterCoordinates configuration matterVariation parameter)
          connectionVariation parameter)
        point direction = _
  rw [holonomicMatterCovariantDerivative_gaugeConnection_expansion,
    holonomicMatterCovariantDerivative_varyMatterCoordinates
      configuration smooth matterVariation parameter point direction]
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
    linkedActiveMatterCovariantJetResponse
    linkedActiveMatterCovariantJetQuadraticResponse
    holonomicMatterVariationCovariantDerivative
    connectionVariation matterVariation
  simp only [varyMatterCoordinates,
    p286InfinitesimalGaugeConnectionVariation_apply,
    p286LinkedActiveMatterVariation_apply,
    matterCoordinateEquiv.symm_apply_apply]
  simp [p286LinkedActiveMatterVariation, matterVariationCoordinateDerivative,
    map_add, matterCoordinateEquiv_symm_real_smul]
  module

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActivePointJetExpansion
