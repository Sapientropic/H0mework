import H0mework.Fock.HistoryConditional.InverseObservationPacketSource
import H0mework.Fock.CopyGraph.TimeEnergyNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationPacket

open SourceGeneratedActionWords SourceCopyTimeModel SourceCopyTimeEnergy
noncomputable section

theorem recovered (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    restore (program.1 - 1) (copyIndex program.1) (packet depth word value) = value := by
  dsimp only
  rw [packet_source, restore_source]

theorem next_packet (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    next (program.1 - 1) (copyIndex program.1) (packet depth word value) =
      packet depth word (SourceJointClockGraph.action value) := by
  dsimp only
  rw [packet_source, packet_source, next_source]

theorem next_recovered (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    restore (program.1 - 1) (copyIndex program.1) (next (program.1 - 1) (copyIndex program.1) (packet depth word value)) =
      SourceJointClockGraph.action value := by
  dsimp only
  rw [next_packet, recovered]

theorem recovery_error (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    value - restore (program.1 - 1) (copyIndex program.1) samples =
      restore (program.1 - 1) (copyIndex program.1) (packet depth word value - samples) := by
  dsimp only
  rw [restore_sub, recovered]

theorem error_budget (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet depth word value - samples
    ‖value - restore (program.1 - 1) (copyIndex program.1) samples‖ ^ 2 + axisCost (program.1 - 1) (copyIndex program.1) residual =
      copyCost (program.1 - 1) (copyIndex program.1) residual +
        ‖mergedMass (program.1 - 1) (copyIndex program.1) residual‖ ^ 2 +
        ‖mergedClock (program.1 - 1) (copyIndex program.1) residual‖ ^ 2 := by
  dsimp only
  rw [recovery_error]
  exact restore_budget _ _ _

theorem next_recovery_error (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceJointClockGraph.action value - restore (program.1 - 1) (copyIndex program.1)
      (next (program.1 - 1) (copyIndex program.1) samples) =
      restore (program.1 - 1) (copyIndex program.1)
        (next (program.1 - 1) (copyIndex program.1) (packet depth word value - samples)) := by
  dsimp only
  rw [map_sub, restore_sub, next_recovered]

theorem next_error_budget (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet depth word value - samples
    ‖SourceJointClockGraph.action value - restore (program.1 - 1) (copyIndex program.1)
      (next (program.1 - 1) (copyIndex program.1) samples)‖ ^ 2 +
      axisCost (program.1 - 1) (copyIndex program.1) (next (program.1 - 1) (copyIndex program.1) residual) =
    copyCost (program.1 - 1) (copyIndex program.1) residual + clockWork (program.1 - 1) (copyIndex program.1) (residual 0) +
      ‖mergedMass (program.1 - 1) (copyIndex program.1) (next (program.1 - 1) (copyIndex program.1) residual)‖ ^ 2 +
      ‖mergedClock (program.1 - 1) (copyIndex program.1) (next (program.1 - 1) (copyIndex program.1) residual)‖ ^ 2 := by
  dsimp only
  rw [next_recovery_error]
  exact next_budget _ _ _

end
end SourceInverseObservationPacket
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
