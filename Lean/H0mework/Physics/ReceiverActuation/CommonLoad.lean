import H0mework.Physics.ReceiverActuation.OutputRecovery

/-! # One physical switch interval loads every commanded channel of the whole receiver -/

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

def commonOutputLoadDuration : SISecond :=
  finiteSamplingClockSampleTime hardware.meteredSource.fixture.coreSource hardware.clockCode
    ⟨(Finset.univ : Finset FiniteEmbodimentChannel).sup'
      ⟨.sourceBound, Finset.mem_univ _⟩
      (fun channel => (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax)
        (technology := technology) downstreamTechnology downstreamGraph channel).value)⟩

theorem commonOutputLoadDuration_covers_channel (channel : FiniteEmbodimentChannel) :
    (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph channel).value ≤
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value :=
  (Finset.le_sup' (fun selected : FiniteEmbodimentChannel =>
    (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax)
      (technology := technology) downstreamTechnology downstreamGraph selected).value) (Finset.mem_univ channel)).trans
    (finiteSamplingClock_requested_le_sampleTime hardware.meteredSource.fixture.coreSource hardware.clockCode _)

theorem commonOutputLoadDuration_pos :
    0 < (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value := by
  have localPositive : 0 < (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax)
      (technology := technology) downstreamTechnology downstreamGraph .sourceBound).value :=
    loadedCapacitorDuration_pos _ _ _ _ _
  exact localPositive.trans_le (commonOutputLoadDuration_covers_channel downstreamTechnology downstreamGraph .sourceBound)

def commonOutputRecoveryStart : SISecond :=
  ⟨(readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value +
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value⟩

theorem commonOutputRecoveryStart_nonnegative :
    0 ≤ (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value :=
  add_nonneg (readDelay_nonneg downstreamTechnology downstreamGraph)
    (commonOutputLoadDuration_pos downstreamTechnology downstreamGraph).le

theorem commonOutputRecoveryStart_after_graph :
    (packetLineReadyTime technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig).value +
      (aigDualRailGraphDeadline technology (aigOutputBank
        (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig).value ≤
      (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value := by
  let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
  let ready := (packetLineReadyTime technology (aigOutputBank entry).aig).value
  have capture := aigInputSampledTime_late technology (aigOutputBank entry).aig ready
    hardware.meteredSource.fixture.coreSource hardware.clockCode
  have read := receiverWholeCaptureTime_le_readTime hardware.adcCode
    ((Nat.log 2 clockMax + 1)) technology ready
    hardware.meteredSource.fixture.coreSource hardware.clockCode downstreamTechnology downstreamGraph
  have load := (commonOutputLoadDuration_pos (hardware := hardware) (clockMax := clockMax)
    (technology := technology) downstreamTechnology downstreamGraph).le
  change ready + (aigDualRailGraphDeadline technology (aigOutputBank entry).aig).value ≤ _
  change _ ≤ (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value at read
  dsimp only [receiverWholeCaptureTime] at read
  dsimp only [commonOutputRecoveryStart]
  linarith

theorem commonOutputRecoveryReady_zero :
    aigBankRecoveryReady technology
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
      (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value = 0 :=
  max_eq_left (sub_nonpos.mpr (commonOutputRecoveryStart_after_graph downstreamTechnology downstreamGraph))

variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def commonOutputLoadRecipient : FiniteDimensionedSeriesRLCPortState where
  voltageAt channel := ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel
    (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value 1⟩
  currentAt channel := ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel
    (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value 2⟩

def commonOutputRecoveryInitial (index : Fin 11) : SIVolt :=
  Fin.cases
    (let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
     current.receiverStateAt downstreamTechnology downstreamGraph
      ⟨((aigOutputBank entry).vec.get 0 (by decide)).gate, ((aigOutputBank entry).vec.get 0 (by decide)).hgate⟩ false
      (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value)
    (fun port => ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph (finiteADCChannelEquivFin.symm port)
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value 0⟩) index

theorem commonOutputRecoveryInitial_is_loaded (channel : FiniteEmbodimentChannel) :
    commonOutputRecoveryInitial downstreamTechnology downstreamGraph current (outputLoadPort channel) =
      ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel
        (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value 0⟩ := by
  change commonOutputRecoveryInitial downstreamTechnology downstreamGraph current (finiteADCChannelEquivFin channel).succ = _
  simp only [commonOutputRecoveryInitial, Fin.cases_succ, Equiv.symm_apply_apply]

theorem commonOutputLoadEnergy_le_half (channel : FiniteEmbodimentChannel) :
    (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value).value ≤
      (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value / 2 := by
  apply capacitorRLCEnergyAt_le_half
  exact (finiteSamplingClock_requested_le_sampleTime hardware.meteredSource.fixture.coreSource hardware.clockCode _).trans
    (commonOutputLoadDuration_covers_channel downstreamTechnology downstreamGraph channel)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
