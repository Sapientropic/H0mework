import H0mework.Physics.LowEnergy.PacketFourier.Pairs
import H0mework.Physics.LowEnergy.PacketFourier.Sine

set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics HistoryPrepared Stage9DEF
noncomputable section

theorem opposite_source_quadratures (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (left right : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (oppositeObservable energy damping positive shift left right)))=
      inner ℂ (packetCurrent energy damping positive shift left) (packetCurrent energy damping positive shift right)+
        inner ℂ (sinePacket energy damping positive shift left) (sinePacket energy damping positive shift right) := by
  rw [opposite_source_read,quadrature_pair]

theorem opposite_source_initial_lower (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    packetNoise energy damping positive shift ≤
      (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (sourceMother (oppositeObservable energy damping positive shift 0 0)))).re := by
  rw [opposite_source_diagonal,Complex.ofReal_re]
  exact original_noise_le_opposite energy damping positive shift

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
