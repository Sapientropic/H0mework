import H0mework.Physics.QuantumState.SourceCoefficients

/-! A quantum coordinate is a restriction of the complete classical carrier.
The root projects this raw field before observation or certification. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Source

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair

noncomputable section

abbrev OccupiedField := BasePoint → Index → ℂ

/-- Preparation reads every occupied coefficient of the supplied full field. -/
def restrict (configuration : StageNineHolonomicConfiguration) : OccupiedField :=
  fun point index => sourceColorDoubletDual index.2
    (configuration.matter point index.1) / 2

theorem restrict_actual : restrict actual = vector := by
  funext point index
  rw [restrict, amplitude_from_actual]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Source
