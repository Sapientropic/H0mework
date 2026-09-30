import H0mework.Fock.HistoryConditional.InverseObservationPacketSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem feedback (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceGWordInverse.recover depth word (time (program.1 + program.2) value) =
      SourceJointClockGraph.action (SourceGWordInverse.recover depth word (time program.2 value)) := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  have split : time (program.1 + program.2) value = time program.2 (time program.1 value) := by
    rw [Nat.add_comm]
    simp only [time, pow_add, mul_apply_eq_comp]
  rw [split, SourceInverseObservationPacket.delayed_observer, SourceInverseObservationPacket.delayed_observer]
  have paid := recover_cycle (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) value
  rw [SourceInverseObservationPacket.copy_scale _ (SourceCompiledWordOperator.slope_positive _)] at paid
  exact paid

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
