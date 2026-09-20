import H0mework.Physics.YangMillsFlatQuantum.Field
import H0mework.Physics.RootRuntime.RecoveryConsumer

/-! The complete Stage1–10 output supplies the response identity at the
current occurrence. Its actual matter and dual evaluate the pure gauge operator. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

private theorem current_mother_response (point : BasePoint)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    Stage10.Runtime.configuration.conjugateMatter point (action (Stage10.Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Compatibility.responseMatrix action) := by
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse point action
  rw [Stage9DEF.Runtime.firstQuantumTick_answer, Stage9DEF.Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.configuration_eq, Stage10.Runtime.tick_vector]
  exact generated

theorem source_mother_curvature (point : BasePoint) (axis : Fin 3) :
    Stage10.Runtime.configuration.conjugateMatter point
      (curvatureAction Flat.sourceConnection point axis (Stage10.Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (curvatureResponse Flat.sourceConnection point axis) :=
  current_mother_response point (curvatureAction Flat.sourceConnection point axis)

theorem source_mother_composite (point : BasePoint) :
    Stage10.Runtime.configuration.conjugateMatter point
      (compositeAction Flat.sourceConnection point (Stage10.Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (compositeResponse Flat.sourceConnection point) :=
  current_mother_response point (compositeAction Flat.sourceConnection point)

end
end SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum
