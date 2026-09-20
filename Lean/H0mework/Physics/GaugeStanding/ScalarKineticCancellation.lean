import H0mework.Physics.GaugeStanding.ScalarCovariantJet
import H0mework.Physics.GaugeStanding.ScalarPairingSkew
import H0mework.Physics.GaugeAction.P286GaugeConnectionActionVariation

/-!
# S9-C: linked active P286 scalar-kinetic cancellation

The linked primitive scalar and connection responses generate
`delta (D H) = rho(epsilon) (D H)`.  The actual degree-four action is skew
for the scalar coordinate pairing, so the complete chart-zero scalar kinetic
first coefficient vanishes pointwise.

No finite-group invariance, Ward receipt, stationarity law, residual zero, or
target variation is accepted at a theorem mouth.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarKineticCancellation

open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveScalarCovariantJet
open StageNineP286LinkedActiveScalarPairingSkew
open StageNineP286LinkedActiveVariation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- The chart-zero scalar kinetic first coefficient vanishes when every
covariant-derivative component is moved by the same actual mother action. -/
theorem scalarGaugeConnectionKineticFirstVariationDensity_motherLieAction_eq_zero
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matrix : SU7MotherLieMatrix) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
        (fun direction =>
          scalarMotherLieAction matrix
            (field.scalarCovariantDerivative direction)) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro first _
  apply Finset.sum_eq_zero
  intro second _
  rw [scalarCoordinatePairingRe_scalarMotherLieAction_skew]
  ring

/-- The complete actual first response of one scalar covariant-jet
component, written from the primitive linked tangent. -/
def linkedActiveScalarCovariantJetResponse
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  fieldDirectionalDerivative
        (fun current =>
          (representationDerivedP286CoupledGaugeTangentSection configuration
            gaugeParameter current).scalar)
        point direction +
      scalarP286ActionBilinear
        ((representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).connection direction)
        (configuration.scalar point) +
    scalarP286ActionBilinear
      (holonomicP286GaugeConnectionCoordinate configuration point direction)
      ((representationDerivedP286CoupledGaugeTangentSection configuration
        gaugeParameter point).scalar)

theorem linkedActiveScalarCovariantJetResponse_eq_action
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    linkedActiveScalarCovariantJetResponse configuration gaugeParameter point
        direction =
      scalarMotherLieAction
        (p286GaugeParameterMotherAt gaugeParameter point)
        (holonomicScalarCovariantDerivative configuration point direction) :=
  linkedActiveScalarCovariantJetVariation_eq_action configuration smooth
    gaugeParameter point direction

/-- The scalar-kinetic contribution to the linked local first variation,
including the unchanged volume density. -/
def linkedActiveScalarKineticFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : ℝ :=
  let field := toContinuumPointField configuration point
  generatedVolumeDensity field *
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
      (linkedActiveScalarCovariantJetResponse configuration gaugeParameter
        point)

/-- Pointwise cancellation of the complete linked scalar-kinetic response. -/
theorem linkedActiveScalarKineticFirstVariationDensity_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    linkedActiveScalarKineticFirstVariationDensity source configuration
        gaugeParameter point =
      0 := by
  unfold linkedActiveScalarKineticFirstVariationDensity
  dsimp only
  rw [show
      linkedActiveScalarCovariantJetResponse configuration gaugeParameter
          point =
        fun direction =>
          scalarMotherLieAction
            (p286GaugeParameterMotherAt gaugeParameter point)
            ((toContinuumPointField configuration point).scalarCovariantDerivative
              direction) by
      funext direction
      exact linkedActiveScalarCovariantJetResponse_eq_action configuration
        smooth gaugeParameter point direction]
  rw [
    scalarGaugeConnectionKineticFirstVariationDensity_motherLieAction_eq_zero,
    mul_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarKineticCancellation
