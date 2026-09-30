import H0mework.Physics.ReceiverActuation.LoadWork
import H0mework.Physics.ReceiverActuation.CommonRecovery
import H0mework.Physics.ReceiverActuation.CommonRecipient

/-! # The complete actual load endpoint is the literal recovery initial state -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

theorem outputLoadReceiverStateAt_eq_recovery_initial
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (polarity : Bool) :
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node polarity
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value =
      commonRecoveryStateAt downstreamTechnology downstreamGraph current node polarity 0 := by
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  by_cases restored : entry.aig.decls.size ≤ node.val ∧ polarity = false
  · let index : Fin 11 := ⟨node.val - entry.aig.decls.size, by
      have size := aigOutputBank_size entry
      have bound : node.val < (aigOutputBank entry).aig.decls.size := node.isLt
      omega⟩
    have sameNode : (⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ : Fin (aigOutputBank entry).aig.decls.size) = node := by
      apply Fin.ext
      dsimp only
      rw [aigOutputBank_ref_gate]
      dsimp only [index]
      omega
    have actualEnd := current.outputLoadReceiverStateAt_common_end downstreamTechnology downstreamGraph index
    dsimp only at actualEnd
    change current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph
      ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false _ = _ at actualEnd
    rw [sameNode, ← restored.2] at actualEnd
    have actualStart := aigBankCommonRecoveryStateAt_output technology entry current.memory current.assignment
      (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
      (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value index 0
    rw [sameNode, ← restored.2, aigBankRecoveryVoltageAt_initial] at actualStart
    exact actualEnd.trans actualStart.symm
  · dsimp only [entry] at restored
    have unloaded : outputLoadChannel? hardware clockMax node polarity = none := by
      unfold outputLoadChannel?
      apply dif_neg
      intro eligible
      exact restored ⟨eligible.1.le, eligible.2⟩
    rw [current.outputLoadReceiverStateAt_unloaded _ _ _ _ _ unloaded]
    simp only [receiverStateAt, aigMemoryStateAt, commonRecoveryStateAt,
      aigHeldBankStateAt, aigBankCommonRecoveryStateAt, dif_neg restored,
      commonOutputRecoveryStart, add_zero]

theorem outputLoadInputVoltageAt_eq_recovery_initial (atom : Std.Tactic.BVDecide.BVBit) :
    current.outputLoadInputVoltageAt downstreamTechnology downstreamGraph atom
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value =
      aigMemoryInputWave technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
        current.memory current.assignment atom
        (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value := rfl

theorem outputLoadWholeStoredEnergyAt_eq_recovery_initial :
    let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
    let offset := (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value
    outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value =
      aigActualStoredEnergy technology (aigOutputBank entry).aig
        (fun atom => aigMemoryInputWave technology entry current.memory current.assignment atom offset)
        (fun node polarity => commonRecoveryStateAt downstreamTechnology downstreamGraph current node polarity 0) +
      drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (commonRecipientRecoveryAt downstreamTechnology downstreamGraph current 0) := by
  dsimp only
  simp only [outputLoadWholeStoredEnergyAt, outputLoadInputVoltageAt_eq_recovery_initial,
    outputLoadReceiverStateAt_eq_recovery_initial, outputLoadRecipientAt_common_end,
    commonRecipientRecoveryAt_initial]

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
