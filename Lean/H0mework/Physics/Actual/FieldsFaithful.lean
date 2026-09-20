import H0mework.Physics.Actual.FieldsCoordinates

/-! Full linear dual recovery and faithfulness of the nine-field real read. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum SU7MotherLieAlgebra DiracExteriorMatterAction

noncomputable section

/-- The independent dual is recovered on the existing matter coordinate basis;
no Hermitian relation between matter and dual is assumed. -/
theorem dual_eq_of_basis_eq
    {left right : Module.Dual ℂ DiracExteriorMatterCarrier}
    (same : ∀ index : MatterCoordinateIndex,
      left (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)) =
        right (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) :
    left = right := by
  apply ((PiLp.basisFun 2 ℂ MatterCoordinateIndex).map matterCoordinateEquiv.symm).ext
  intro index
  simpa only [Module.Basis.map_apply, PiLp.basisFun_apply] using same index

theorem configuration_eq_of_realCoordinate_eq
    {left right : StageNineHolonomicConfiguration}
    (same : ∀ coordinate point,
      realCoordinate left coordinate point = realCoordinate right coordinate point) :
    left = right := by
  apply StageNineHolonomicConfiguration.ext
  · funext point row column
    exact same (.coframe row column) point
  · funext point direction row column
    exact same (.gravityConnection direction row column) point
  · funext point internalPair spacetimePair
    exact same (.gravityAuxiliary internalPair spacetimePair) point
  · funext point internalPair spacetimePair
    exact same (.gravitySimplicityMultiplier internalPair spacetimePair) point
  · funext point direction
    apply p286CoordinateEquiv.injective
    apply PiLp.ext
    intro index
    exact same (.gaugeConnection direction index) point
  · funext point pair
    apply p286CoordinateEquiv.injective
    apply PiLp.ext
    intro index
    exact same (.gaugeAuxiliary pair index) point
  · funext point
    apply PiLp.ext
    intro index
    exact complex_eq_of_parts_eq (fun part => same (.scalar index part) point)
  · funext point
    apply matterCoordinateEquiv.injective
    apply PiLp.ext
    intro index
    exact complex_eq_of_parts_eq (fun part => same (.matter index part) point)
  · funext point
    apply dual_eq_of_basis_eq
    intro index
    exact complex_eq_of_parts_eq (fun part => same (.conjugateMatter index part) point)

theorem realCoordinate_injective : Function.Injective realCoordinate := by
  intro left right same
  apply configuration_eq_of_realCoordinate_eq
  intro coordinate point
  exact congrFun (congrFun same coordinate) point

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fields
