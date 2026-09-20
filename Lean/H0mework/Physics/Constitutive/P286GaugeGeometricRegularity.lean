import H0mework.Physics.Constitutive.P286GaugeGeometricKinematics
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity

/-!
# Regularity of the form-native P286 geometric response

This module proves continuity of the actual `D_A B` three-form directly from
the smooth primitive P286 connection and auxiliary field.  The derivative
part is generated from the actual Fréchet derivative of the auxiliary field;
the algebraic part uses only continuity of the representation-derived P286
Lie bracket.

Historical volume/Hodge BF momentum, current, Euler, weak equation,
stationarity, auxiliary equation, fixed actual, and residual-zero receipts
are not consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeGeometricRegularity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Smoothness of the complete faithful P286 auxiliary-coordinate field,
assembled from the primitive configuration smoothness. -/
theorem holonomicFormNativeP286GaugeAuxiliaryCoordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate configuration) := by
  apply contDiff_pi'
  intro pair
  exact smooth.2.2.2.2.2.1 pair

/-- Continuity of the actual directional derivative of the primitive P286
auxiliary field. -/
theorem p286GaugeAuxiliaryDirectionalDerivative_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    Continuous
      (p286GaugeAuxiliaryDirectionalDerivative configuration · direction) := by
  change Continuous fun point =>
    fderiv ℝ (holonomicP286GaugeAuxiliaryCoordinate configuration) point
      (coordinateDirection direction)
  have derivativeContinuous : Continuous
      (fderiv ℝ (holonomicP286GaugeAuxiliaryCoordinate configuration)) :=
    ((holonomicFormNativeP286GaugeAuxiliaryCoordinate_contDiff configuration
      smooth).fderiv_right (m := 0) (by simp)).continuous
  exact derivativeContinuous.clm_apply continuous_const

theorem orderedP286GaugeTwoFormComponent_continuous
    (form : BasePoint → P286GaugeTwoForm)
    (formContinuous : Continuous form)
    (first second : LorentzianIndex) :
    Continuous fun point =>
      orderedP286GaugeTwoFormComponent (form point) first second := by
  unfold orderedP286GaugeTwoFormComponent
  apply continuous_finsetSum
  intro pair _
  exact
    (continuous_const : Continuous fun _ : BasePoint =>
      (orientedLorentzBivectorBasisCoefficient pair first second : ℝ)).smul
      ((continuous_apply pair).comp formContinuous)

theorem p286GaugeTwoFormAdjoint_continuous
    (generator : BasePoint → P286CoordinateCarrier)
    (form : BasePoint → P286GaugeTwoForm)
    (generatorContinuous : Continuous generator)
    (formContinuous : Continuous form) :
    Continuous fun point =>
      p286GaugeTwoFormAdjoint (generator point) (form point) := by
  apply continuous_pi
  intro pair
  exact p286CoordinateLieBracket_apply_continuous generator
    (fun point => form point pair) generatorContinuous
    ((continuous_apply pair).comp formContinuous)

theorem pointwiseP286GaugeTwoFormCovariantDerivative_continuous
    (connection : BasePoint → P286GaugeOneForm)
    (value : BasePoint → P286GaugeTwoForm)
    (derivative : LorentzianIndex → BasePoint → P286GaugeTwoForm)
    (connectionContinuous : Continuous connection)
    (valueContinuous : Continuous value)
    (derivativeContinuous : ∀ direction, Continuous (derivative direction))
    (direction : LorentzianIndex) :
    Continuous fun point =>
      pointwiseP286GaugeTwoFormCovariantDerivative
        (connection point) (value point)
        (fun derivativeDirection => derivative derivativeDirection point)
        direction := by
  unfold pointwiseP286GaugeTwoFormCovariantDerivative
  exact (derivativeContinuous direction).add
    (p286GaugeTwoFormAdjoint_continuous
      (fun point => connection point direction) value
      ((continuous_apply direction).comp connectionContinuous)
      valueContinuous)

theorem pointwiseP286GaugeTwoFormExteriorCovariantDerivative_continuous
    (connection : BasePoint → P286GaugeOneForm)
    (value : BasePoint → P286GaugeTwoForm)
    (derivative : LorentzianIndex → BasePoint → P286GaugeTwoForm)
    (connectionContinuous : Continuous connection)
    (valueContinuous : Continuous value)
    (derivativeContinuous : ∀ direction, Continuous (derivative direction)) :
    Continuous fun point =>
      pointwiseP286GaugeTwoFormExteriorCovariantDerivative
        (connection point) (value point)
        (fun direction => derivative direction point) := by
  apply continuous_pi
  intro triple
  have covariantContinuous : ∀ direction,
      Continuous fun point =>
        pointwiseP286GaugeTwoFormCovariantDerivative
          (connection point) (value point)
          (fun derivativeDirection => derivative derivativeDirection point)
          direction :=
    pointwiseP286GaugeTwoFormCovariantDerivative_continuous connection value
      derivative connectionContinuous valueContinuous derivativeContinuous
  unfold pointwiseP286GaugeTwoFormExteriorCovariantDerivative
  exact
    ((orderedP286GaugeTwoFormComponent_continuous
      (fun point =>
        pointwiseP286GaugeTwoFormCovariantDerivative
          (connection point) (value point)
          (fun derivativeDirection => derivative derivativeDirection point)
          (threeFormFirst triple))
      (covariantContinuous (threeFormFirst triple))
      (threeFormSecond triple) (threeFormThird triple)).add
    (orderedP286GaugeTwoFormComponent_continuous
      (fun point =>
        pointwiseP286GaugeTwoFormCovariantDerivative
          (connection point) (value point)
          (fun derivativeDirection => derivative derivativeDirection point)
          (threeFormSecond triple))
      (covariantContinuous (threeFormSecond triple))
      (threeFormThird triple) (threeFormFirst triple))).add
    (orderedP286GaugeTwoFormComponent_continuous
      (fun point =>
        pointwiseP286GaugeTwoFormCovariantDerivative
          (connection point) (value point)
          (fun derivativeDirection => derivative derivativeDirection point)
          (threeFormThird triple))
      (covariantContinuous (threeFormThird triple))
      (threeFormFirst triple) (threeFormSecond triple))

/-- The complete actual form-native geometric response `D_A B` is
continuous. -/
theorem holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous
      (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        configuration) := by
  exact pointwiseP286GaugeTwoFormExteriorCovariantDerivative_continuous
    (holonomicP286GaugeConnectionCoordinate configuration)
    (holonomicP286GaugeAuxiliaryCoordinate configuration)
    (fun direction point =>
      p286GaugeAuxiliaryDirectionalDerivative configuration point direction)
    (holonomicP286GaugeConnectionCoordinate_continuous configuration smooth)
    (holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth)
    (p286GaugeAuxiliaryDirectionalDerivative_continuous configuration smooth)

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeGeometricRegularity
