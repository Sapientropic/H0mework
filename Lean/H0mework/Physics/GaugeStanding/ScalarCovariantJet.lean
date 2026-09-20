import H0mework.Physics.GaugeStanding.LieRepresentation
import H0mework.Physics.GaugeStanding.ScalarJetAlgebra

/-!
# S9-C: linked active scalar covariant jet

The same compactly supported P286 parameter that moves the primitive
connection and scalar also moves the complete scalar covariant jet.  The
result is the actual infinitesimal representation law

`delta (D H) = rho(epsilon) (D H)`.

The proof combines the variable-parameter product rule, the action-generated
connection direction `delta A = [epsilon, A] - d epsilon`, and the faithful
P286 representation bracket.  It does not accept a Ward identity,
stationarity law, residual-zero receipt, or target jet as a premise.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarCovariantJet

open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveLieRepresentation
open StageNineP286LinkedActiveScalarJetAlgebra
open StageNineP286LinkedActiveVariation

noncomputable section

set_option autoImplicit false

/-- The complete first variation of the scalar covariant jet along the linked
active P286 tangent is the action of the same parameter on the original
covariant jet. -/
theorem linkedActiveScalarCovariantJetVariation_eq_action
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (direction : LorentzianIndex) :
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
          gaugeParameter point).scalar) =
    scalarMotherLieAction
      (p286GaugeParameterMotherAt gaugeParameter point)
      (holonomicScalarCovariantDerivative configuration point direction) := by
  let epsilon := gaugeParameter point
  let connection :=
    holonomicP286GaugeConnectionCoordinate configuration point direction
  let parameterDerivative :=
    p286GaugeParameterDerivative gaugeParameter point direction
  let scalar := configuration.scalar point
  let scalarDerivative :=
    fieldDirectionalDerivative configuration.scalar point direction
  have connectionTangent :
      (representationDerivedP286CoupledGaugeTangentSection configuration
        gaugeParameter point).connection direction =
        coordinateBracket epsilon connection - parameterDerivative := by
    rfl
  have scalarTangent :
      (representationDerivedP286CoupledGaugeTangentSection configuration
        gaugeParameter point).scalar =
        scalarP286ActionBilinear epsilon scalar := by
    rfl
  have targetAction :
      scalarMotherLieAction
          (p286GaugeParameterMotherAt gaugeParameter point)
          (holonomicScalarCovariantDerivative configuration point direction) =
        scalarP286ActionBilinear epsilon
          (scalarDerivative +
            scalarP286ActionBilinear connection scalar) := by
    simp [epsilon, connection, scalar, scalarDerivative,
      p286GaugeParameterMotherAt, holonomicScalarCovariantDerivative,
      holonomicP286GaugeConnectionCoordinate, scalarP286ActionBilinear]
  rw [fieldDirectionalDerivative_linkedActiveScalar configuration smooth,
    connectionTangent, scalarTangent, targetAction]
  rw [show
      scalarP286ActionBilinear
          (coordinateBracket epsilon connection - parameterDerivative)
          scalar =
        scalarP286ActionBilinear (coordinateBracket epsilon connection)
            scalar -
          scalarP286ActionBilinear parameterDerivative scalar by
      rw [map_sub, LinearMap.sub_apply]]
  rw [scalarP286ActionBilinear_coordinateBracket]
  rw [map_add]
  abel

end

end SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarCovariantJet
