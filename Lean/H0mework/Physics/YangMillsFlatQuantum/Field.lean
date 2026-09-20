import H0mework.Physics.YangMillsAction.FlatConsumer
import H0mework.Physics.CompositeSpectrum.Action

/-! Pure gauge curvature is passed to the already generated full mother
action and its independent-dual quantum response. The source state is retained. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum

open DiracExteriorMatterAction SU7MotherLieAlgebra
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9DEF

noncomputable section

def curvatureAction (connection : P286ConnectionField) (point : BasePoint) (axis : Fin 3) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracExteriorMotherLieAction
    (p286LieBlockEmbed (holonomicGaugeCurvature (Flat.configuration connection) point
      (Stage10.GaugeSpectrum.magneticPair axis)))

def curvatureResponse (connection : P286ConnectionField) (point : BasePoint) (axis : Fin 3) : State.Observable :=
  Compatibility.responseMatrix (curvatureAction connection point axis)

def compositeAction (connection : P286ConnectionField) (point : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Stage10.GaugeSpectrum.alternatingProduct (curvatureAction connection point)

def compositeResponse (connection : P286ConnectionField) (point : BasePoint) : State.Observable :=
  Compatibility.responseMatrix (compositeAction connection point)

theorem source_action (point : BasePoint) (axis : Fin 3) :
    curvatureAction Flat.sourceConnection point axis = Stage10.GaugeSpectrum.incomingCurvatureAction point axis := by
  rw [curvatureAction, Flat.source_curvature_preserved]
  rfl

theorem source_response (point : BasePoint) (axis : Fin 3) :
    curvatureResponse Flat.sourceConnection point axis = Stage10.GaugeSpectrum.dualCurvature point axis := by
  rw [curvatureResponse, source_action, Stage10.GaugeSpectrum.incomingCurvatureAction_eq]
  rfl

theorem source_composite_action (point : BasePoint) :
    compositeAction Flat.sourceConnection point = Stage10.GaugeSpectrum.compositeAction point :=
  congrArg Stage10.GaugeSpectrum.alternatingProduct (funext (source_action point))

theorem source_composite_response (point : BasePoint) :
    compositeResponse Flat.sourceConnection point = Stage10.GaugeSpectrum.cubic point := by
  rw [compositeResponse, source_composite_action, Stage10.GaugeSpectrum.compositeAction_responseMatrix]

end
end SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum
