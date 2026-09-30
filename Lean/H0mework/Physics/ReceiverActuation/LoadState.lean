import H0mework.Physics.ReceiverActuation.LoadIncidence

/-!
# The whole receiver and recipient during one actual connected-load interval

Only the ten literal command capacitors use their generated U coordinates.
All other receiver coordinates and registered inputs retain the original
history. The raw sheet carries no rail claim and no replacement memory value.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

/-- This sheet follows the same read event; intermediate loaded U is not asserted to be in rail. -/
def outputLoadReceiverStateAt
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (polarity : Bool) (time : ℝ) : SIVolt :=
  match outputLoadChannel? hardware clockMax node polarity with
  | some channel => ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel time 0⟩
  | none => current.receiverStateAt downstreamTechnology downstreamGraph node polarity
      ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value + time)

def outputLoadInputVoltageAt (atom : BVBit) (time : ℝ) : SIVolt :=
  aigMemoryInputWave technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    current.memory current.assignment atom
    ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value + time)

/-- V and I read the same matrix-exponential occurrence and the same elapsed load time as U. -/
def outputLoadRecipientAt (time : ℝ) : FiniteDimensionedSeriesRLCPortState where
  voltageAt channel := ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel time 1⟩
  currentAt channel := ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel time 2⟩

theorem outputLoadInputVoltageAt_initial (atom : BVBit) :
    current.outputLoadInputVoltageAt downstreamTechnology downstreamGraph atom 0 =
      aigMemoryInputWave technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
        current.memory current.assignment atom
        (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value := by
  simp only [outputLoadInputVoltageAt, add_zero]

theorem outputLoadReceiverStateAt_command (channel : FiniteEmbodimentChannel) (time : ℝ) :
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph
      (outputLoadNode hardware clockMax channel) false time =
      ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel time 0⟩ := by
  simp only [outputLoadReceiverStateAt, outputLoadChannel?_command]

theorem outputLoadReceiverStateAt_unloaded
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (polarity : Bool) (time : ℝ) (unloaded : outputLoadChannel? hardware clockMax node polarity = none) :
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node polarity time =
      current.receiverStateAt downstreamTechnology downstreamGraph node polarity
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time) := by
  simp only [outputLoadReceiverStateAt, unloaded]

theorem outputLoadReceiverStateAt_negative
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (time : ℝ) :
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node true time =
      current.receiverStateAt downstreamTechnology downstreamGraph node true
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time) :=
  current.outputLoadReceiverStateAt_unloaded downstreamTechnology downstreamGraph node true time
    (outputLoadChannel?_negative hardware clockMax node)

theorem outputLoadReceiverStateAt_old
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (old : node.val < (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size)
    (polarity : Bool) (time : ℝ) :
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node polarity time =
      current.receiverStateAt downstreamTechnology downstreamGraph node polarity
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time) :=
  current.outputLoadReceiverStateAt_unloaded downstreamTechnology downstreamGraph node polarity time
    (outputLoadChannel?_old hardware clockMax node old polarity)

theorem outputLoadReceiverStateAt_validity (time : ℝ) :
    let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
    let node : Fin (aigOutputBank entry).aig.decls.size :=
      ⟨((aigOutputBank entry).vec.get 0 (by decide)).gate, ((aigOutputBank entry).vec.get 0 (by decide)).hgate⟩
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node false time =
      current.receiverStateAt downstreamTechnology downstreamGraph node false
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time) :=
  current.outputLoadReceiverStateAt_unloaded downstreamTechnology downstreamGraph _ false time
    (outputLoadChannel?_validity hardware clockMax)

/-- Connection preserves every coordinate of the complete actual receiver snapshot. -/
theorem outputLoadReceiverStateAt_initial
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (polarity : Bool) :
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node polarity 0 =
      current.receiverStateAt downstreamTechnology downstreamGraph node polarity
        (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value := by
  unfold outputLoadReceiverStateAt
  cases selected : outputLoadChannel? hardware clockMax node polarity with
  | none => simp only [add_zero]
  | some channel =>
    obtain ⟨rfl, rfl⟩ := (outputLoadChannel?_some_iff hardware clockMax node polarity channel).mp selected
    dsimp only
    apply SIQuantity.ext
    exact congrArg (fun state : Fin 3 → ℝ => state 0)
      (current.outputLoadStateAt_initial downstreamTechnology downstreamGraph channel)

theorem outputLoadRecipientAt_initial :
    current.outputLoadRecipientAt downstreamTechnology downstreamGraph 0 =
      current.outputLoadInitialRecipient downstreamTechnology downstreamGraph := by
  apply FiniteDimensionedSeriesRLCPortState.ext <;> funext channel
  all_goals
    apply SIQuantity.ext
    simp only [outputLoadRecipientAt, current.outputLoadStateAt_initial]
    rfl

theorem outputLoadRecipientAt_common_end :
    current.outputLoadRecipientAt downstreamTechnology downstreamGraph
        (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value =
      commonOutputLoadRecipient downstreamTechnology downstreamGraph current := rfl

/-- All eleven recovery initials, including validity, come from this one common-time sheet. -/
theorem outputLoadReceiverStateAt_common_end (index : Fin 11) :
    let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
    current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph
      ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value =
      commonOutputRecoveryInitial downstreamTechnology downstreamGraph current index := by
  dsimp only
  refine Fin.cases ?_ (fun port => ?_) index
  · simpa only [Fin.val_zero, commonOutputRecoveryInitial, Fin.cases_zero, commonOutputRecoveryStart] using
      current.outputLoadReceiverStateAt_validity downstreamTechnology downstreamGraph
        (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value
  · let channel := finiteADCChannelEquivFin.symm port
    have port_eq : outputLoadPort channel = port.succ := by
      change (finiteADCChannelEquivFin (finiteADCChannelEquivFin.symm port)).succ = port.succ
      exact congrArg Fin.succ (finiteADCChannelEquivFin.apply_symm_apply port)
    have actual := current.outputLoadReceiverStateAt_command downstreamTechnology downstreamGraph channel
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value
    have target := commonOutputRecoveryInitial_is_loaded downstreamTechnology downstreamGraph current channel
    rw [port_eq] at target
    rw [target]
    simpa only [outputLoadNode, port_eq] using actual

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
