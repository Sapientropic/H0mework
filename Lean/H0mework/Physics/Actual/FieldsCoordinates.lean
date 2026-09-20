import H0mework.Physics.Holonomic.HolonomicField

/-! Finite real coordinates of all nine primitive fields. Complex scalar,
matter and independent dual coordinates retain both real and imaginary parts. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum SU7MotherLieAlgebra

noncomputable section

local instance p286Finite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance p286Fintype : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance matterFintype : Fintype MatterCoordinateIndex := Fintype.ofFinite _

inductive Coordinate
  | coframe : LorentzianIndex → LorentzianIndex → Coordinate
  | gravityConnection : LorentzianIndex → LorentzianIndex → LorentzianIndex → Coordinate
  | gravityAuxiliary : Fin 6 → Fin 6 → Coordinate
  | gravitySimplicityMultiplier : Fin 6 → Fin 6 → Coordinate
  | gaugeConnection : LorentzianIndex → P286CoordinateIndex → Coordinate
  | gaugeAuxiliary : Fin 6 → P286CoordinateIndex → Coordinate
  | scalar : ScalarBasisIndex → Bool → Coordinate
  | matter : MatterCoordinateIndex → Bool → Coordinate
  | conjugateMatter : MatterCoordinateIndex → Bool → Coordinate
  deriving Fintype

def complexPart : Bool → ℂ → ℝ
  | false => Complex.re
  | true => Complex.im

def realCoordinate (configuration : StageNineHolonomicConfiguration)
    (coordinate : Coordinate) (point : BasePoint) : ℝ :=
  match coordinate with
  | .coframe row column => configuration.coframe point row column
  | .gravityConnection direction row column =>
      configuration.gravityConnection point direction row column
  | .gravityAuxiliary internalPair spacetimePair =>
      configuration.gravityAuxiliary point internalPair spacetimePair
  | .gravitySimplicityMultiplier internalPair spacetimePair =>
      configuration.gravitySimplicityMultiplier point internalPair spacetimePair
  | .gaugeConnection direction index =>
      p286CoordinateEquiv (configuration.gaugeConnection point direction) index
  | .gaugeAuxiliary pair index =>
      p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) index
  | .scalar index part => complexPart part (configuration.scalar point index)
  | .matter index part =>
      complexPart part (matterCoordinateEquiv (configuration.matter point) index)
  | .conjugateMatter index part =>
      complexPart part (configuration.conjugateMatter point
        (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)))

theorem complex_eq_of_parts_eq {left right : ℂ}
    (same : ∀ part, complexPart part left = complexPart part right) : left = right :=
  Complex.ext (same false) (same true)

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fields
