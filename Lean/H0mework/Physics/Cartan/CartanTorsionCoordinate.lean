import H0mework.Physics.Holonomic.HolonomicField

/-!
# Dependency-light Cartan torsion coordinate

This module exposes the domain-native Cartan torsion coordinate without
importing any historical Stage-9 response constructor.  It is a direct
readout of a primitive coframe and gravity connection, not a residual slot,
stationarity receipt, or torsion-free assumption.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCartanActionCoframeSecondJetLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-- Domain-native Cartan torsion coordinate, defined independently of every
Stage-9 residual carrier and response constructor. -/
def cartanTorsionCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (first second internal : LorentzianIndex) : ℝ :=
  fieldDirectionalDerivative
      (fun candidate =>
        configuration.coframe candidate internal second)
      point first -
    fieldDirectionalDerivative
      (fun candidate =>
        configuration.coframe candidate internal first)
      point second +
    ∑ middle : LorentzianIndex,
      configuration.gravityConnection point first internal middle *
        configuration.coframe point middle second -
    ∑ middle : LorentzianIndex,
      configuration.gravityConnection point second internal middle *
        configuration.coframe point middle first

end

end
  SaturationMonoid.PhysicsCore.StageNineCartanActionCoframeSecondJetLocalActualLift
