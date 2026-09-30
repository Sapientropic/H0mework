import H0mework.Fock.CopyGraph.TimeGramDecoder

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index)
open SourceCopyTimeModel (Packet phases ExistingModel modelPoint modelStep modelPhases modelRestore next)
noncomputable section

def model (depth : Nat) (index : Index depth) (packet : Packet depth index) : ExistingModel depth index :=
  modelPoint depth index (decode depth index packet)

theorem model_value (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    modelRestore depth index (model depth index packet) = decode depth index packet :=
  SourceCopyTimeModel.model_restore_source depth index _

theorem model_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    model depth index (phases depth index value) = modelPoint depth index value := by
  rw [model, decode_source]

theorem model_next (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    modelPhases depth index (modelStep depth index (model depth index packet)) =
      next depth index (modelPhases depth index (model depth index packet)) :=
  SourceCopyTimeModel.model_phases_next depth index (model depth index packet)

theorem complete_fibre (depth : Nat) (index : Index depth) (left right : Packet depth index) :
    left = right ↔ model depth index left = model depth index right ∧ residual depth index left = residual depth index right := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨sameModel, sameResidual⟩
    have sameValue := congrArg (modelRestore depth index) sameModel
    rw [model_value, model_value] at sameValue
    have sameFrame := reconstruction depth index left
    rw [sameValue, sameResidual, reconstruction] at sameFrame
    exact (WithLp.toLp_injective 2 sameFrame).symm

theorem decode_sub (depth : Nat) (index : Index depth) (left right : Packet depth index) :
    decode depth index (left - right) = decode depth index left - decode depth index right := by
  apply normal_injective depth index
  change (analysis depth index).adjoint (analysis depth index (decode depth index (left - right))) =
    (analysis depth index).adjoint (analysis depth index (decode depth index left - decode depth index right))
  rw [normal_equation, WithLp.toLp_sub, map_sub, map_sub, map_sub, normal_equation, normal_equation]

theorem residual_packet (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    WithLp.ofLp (residual depth index packet) = packet - phases depth index (decode depth index packet) := by
  rw [residual, analysis_packet, ← WithLp.toLp_sub]

theorem decode_residual (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    decode depth index (WithLp.ofLp (residual depth index packet)) = 0 := by
  apply normal_injective depth index
  change (analysis depth index).adjoint (analysis depth index (decode depth index (WithLp.ofLp (residual depth index packet)))) =
    (analysis depth index).adjoint (analysis depth index 0)
  rw [normal_equation, WithLp.toLp_ofLp, residual_normal, map_zero, map_zero]

theorem next_correction (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    decode depth index (next depth index packet) - SourceJointClockGraph.action (decode depth index packet) =
      decode depth index (next depth index (WithLp.ofLp (residual depth index packet))) := by
  rw [residual_packet, map_sub, decode_sub, SourceCopyTimeModel.next_source, decode_source]

theorem model_next_correction (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    model depth index (next depth index packet) =
      modelStep depth index (model depth index packet) +
        modelPoint depth index (decode depth index (next depth index (WithLp.ofLp (residual depth index packet)))) := by
  have actual := next_correction depth index packet
  have after : decode depth index (next depth index packet) = SourceJointClockGraph.action (decode depth index packet) +
      decode depth index (next depth index (WithLp.ofLp (residual depth index packet))) := by
    rw [← actual]
    abel
  rw [model, after, map_add]
  congr 1

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
