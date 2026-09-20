import H0mework.Physics.Holonomic.HolonomicField

/-!
# Holonomic gauge-curvature transport

Gauge curvature is determined by the full gauge-connection field.  This
dependency-light transporter keeps that generic fact out of fixed P506
producer modules.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicGaugeCurvatureTransport

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

theorem holonomicGaugeCurvature_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gaugeConnection = second.gaugeConnection)
    (point : BasePoint) :
    holonomicGaugeCurvature first point =
      holonomicGaugeCurvature second point := by
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [connectionEq]

end

end SaturationMonoid.PhysicsCore.StageNineHolonomicGaugeCurvatureTransport
