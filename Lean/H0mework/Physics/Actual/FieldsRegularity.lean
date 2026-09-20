import H0mework.Physics.Actual.FieldsCoordinates

/-! The original nine-field smoothness contract supplies every real coordinate. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

attribute [local instance] p286Finite p286Fintype matterFintype

theorem complexPart_contDiff (part : Bool) : ContDiff ℝ ∞ (complexPart part) := by
  cases part
  · exact Complex.reCLM.contDiff
  · exact Complex.imCLM.contDiff

theorem realCoordinate_contDiff
    {configuration : StageNineHolonomicConfiguration}
    (smooth : configuration.Smooth) (coordinate : Coordinate) :
    ContDiff ℝ ∞ (realCoordinate configuration coordinate) := by
  rcases smooth with ⟨coframe, gravityConnection, gravityAuxiliary,
    gravitySimplicityMultiplier, gaugeConnection, gaugeAuxiliary, scalar, matter, dual⟩
  cases coordinate with
  | coframe row column => exact coframe row column
  | gravityConnection direction row column => exact gravityConnection direction row column
  | gravityAuxiliary internalPair spacetimePair => exact gravityAuxiliary internalPair spacetimePair
  | gravitySimplicityMultiplier internalPair spacetimePair =>
      exact gravitySimplicityMultiplier internalPair spacetimePair
  | gaugeConnection direction index =>
      exact (contDiff_piLp_apply 2).comp (gaugeConnection direction)
  | gaugeAuxiliary pair index =>
      exact (contDiff_piLp_apply 2).comp (gaugeAuxiliary pair)
  | scalar index part =>
      exact (complexPart_contDiff part).comp ((contDiff_piLp_apply 2).comp scalar)
  | matter index part =>
      exact (complexPart_contDiff part).comp ((contDiff_piLp_apply 2).comp matter)
  | conjugateMatter index part => exact (complexPart_contDiff part).comp (dual index)

theorem realCoordinate_continuous
    {configuration : StageNineHolonomicConfiguration}
    (smooth : configuration.Smooth) (coordinate : Coordinate) :
    Continuous (realCoordinate configuration coordinate) :=
  (realCoordinate_contDiff smooth coordinate).continuous

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fields
