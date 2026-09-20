import H0mework.Physics.GaugeStanding.Variation

/-!
# Stage-9 P286 frozen-source scalar torque

The linked active P286 path moves every charged primitive field while keeping
the proof-free source fixed.  This module isolates the scalar-potential part
of the root-action first variation with its action sign intact.

No action-invariance premise, Ward certificate, equation, residual zero, or
stationarity receipt is accepted.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286FrozenSourceScalarTorque

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveVariation
open StageNineScalarVariation

noncomputable section

set_option autoImplicit false

/-- The chart-zero scalar torque left by an active P286 variation when the
source-generated vacuum is held fixed.  The leading minus sign is inherited
from the `- generatedScalarPotential` term in the root action. -/
def p286FrozenSourceScalarTorqueDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) : ℝ :=
  -(generatedVolumeDensity
      (toContinuumPointField configuration point) *
    scalarPotentialFirstVariation source
      (toContinuumPointField configuration point)
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).scalar)

/-- Direct coordinate expansion of the honest frozen-source carrier.  This
identity uses only the actual quadratic potential gradient; it does not
assume that the derived scalar Lie action is skew for the real pairing. -/
theorem p286FrozenSourceScalarTorqueDensity_eq_gradientPairing
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286FrozenSourceScalarTorqueDensity source configuration gaugeParameter
        point =
      -2 *
        generatedVolumeDensity
          (toContinuumPointField configuration point) *
        scalarCoordinateRealPairing
          ((toContinuumPointField configuration point).scalar -
            sourceGeneratedVacuumCoordinates source)
          (representationDerivedP286CoupledGaugeTangentAt configuration
            gaugeParameter point).scalar := by
  simp [p286FrozenSourceScalarTorqueDensity, scalarPotentialFirstVariation,
    frameRelativeScalarGradient]
  ring_nf

end

end SaturationMonoid.PhysicsCore.StageNineP286FrozenSourceScalarTorque
