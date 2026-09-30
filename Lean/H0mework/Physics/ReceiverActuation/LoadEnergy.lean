import H0mework.Physics.ReceiverActuation.LoadState
import H0mework.Physics.ADCRuntime.LoadedReceiverPhaseWork
import H0mework.Physics.DrivenEnergy.RLCBankWork

/-! # Complete load-phase energy preserves every unaffected physical coordinate -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

private theorem sum_singleton_lookup {Address Channel : Type} [Fintype Address] [Fintype Channel]
    (addressOf : Channel → Address) (lookup : Address → Option Channel)
    (exactLookup : ∀ address channel, lookup address = some channel ↔ address = addressOf channel)
    (value : Channel → ℝ) :
    (∑ address, (lookup address).elim 0 value) = ∑ channel, value channel := by
  classical
  calc
    _ = ∑ address, ∑ channel, if lookup address = some channel then value channel else 0 := by
      apply Finset.sum_congr rfl
      intro address _
      cases lookup address <;> simp
    _ = ∑ channel, ∑ address, if address = addressOf channel then value channel else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro channel _
      apply Finset.sum_congr rfl
      intro address _
      simp only [exactLookup]
    _ = _ := by simp

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

/-- The exact lookup partitions physical addresses, including every unactuated row. -/
theorem outputLoad_unloaded_address_sum
    (energy : AIGCapacitorAddress (aigOutputBank
      (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig → ℝ) :
    (∑ address, if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address else 0) =
      (∑ address, energy address) - ∑ channel, energy (outputLoadAddress hardware clockMax channel) := by
  have rows (address : AIGCapacitorAddress (aigOutputBank
      (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig) :
      energy address =
        (if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address else 0) +
        (outputLoadChannel? hardware clockMax address.val.1 address.val.2).elim 0
          (fun channel => energy (outputLoadAddress hardware clockMax channel)) := by
    cases selected : outputLoadChannel? hardware clockMax address.val.1 address.val.2 with
    | none => simp
    | some channel =>
      rw [(outputLoadChannel?_address_iff hardware clockMax address channel).mp selected]
      simp
  have summed := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun address _ => rows address)
  rw [Finset.sum_add_distrib, sum_singleton_lookup (outputLoadAddress hardware clockMax)
    (fun address => outputLoadChannel? hardware clockMax address.val.1 address.val.2)
    (outputLoadChannel?_address_iff hardware clockMax)] at summed
  linarith

def outputLoadWholeStoredEnergyAt (time : ℝ) : SIJoule :=
  aigActualStoredEnergy technology (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig
    (fun atom => current.outputLoadInputVoltageAt downstreamTechnology downstreamGraph atom time)
    (fun node polarity => current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph node polarity time) +
  drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (current.outputLoadRecipientAt downstreamTechnology downstreamGraph time)

def outputLoadOldCapEnergyAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIJoule :=
  ⟨(outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel).capacitance.value / 2 *
    (current.receiverStateAt downstreamTechnology downstreamGraph (outputLoadNode hardware clockMax channel) false
      ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value + time)).value ^ 2⟩

def outputLoadCapEnergyAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIJoule :=
  ⟨(outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel).capacitance.value / 2 *
    current.outputLoadStateAt downstreamTechnology downstreamGraph channel time 0 ^ 2⟩

theorem outputLoadWholeStoredEnergyAt_initial :
    outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current 0 =
      receiverStoredEnergyAt downstreamTechnology downstreamGraph current
        (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value +
      drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (current.outputLoadInitialRecipient downstreamTechnology downstreamGraph) := by
  unfold outputLoadWholeStoredEnergyAt
  rw [current.outputLoadRecipientAt_initial, receiverStoredEnergyAt_is_state_projection]
  congr 2
  · funext atom
    exact current.outputLoadInputVoltageAt_initial _ _ atom
  · funext node polarity
    exact current.outputLoadReceiverStateAt_initial _ _ node polarity

/-- A complete sheet changes exactly the ten addressed capacitor rows; no old-prefix energy is dropped. -/
theorem outputLoadWholeStoredEnergyAt_decomposition (time : ℝ) :
    (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current time).value =
      (receiverStoredEnergyAt downstreamTechnology downstreamGraph current
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time)).value -
      (∑ channel, (outputLoadOldCapEnergyAt downstreamTechnology downstreamGraph current channel time).value) +
      (∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel time).value) := by
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  let old : AIGCapacitorAddress (aigOutputBank entry).aig → ℝ := fun address =>
    (compileDualRailCell technology (aigOutputBank entry).aig address.val.1 address.val.2).capacitance.value / 2 *
      (current.receiverStateAt downstreamTechnology downstreamGraph address.val.1 address.val.2
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time)).value ^ 2
  let actual : AIGCapacitorAddress (aigOutputBank entry).aig → ℝ := fun address =>
    (compileDualRailCell technology (aigOutputBank entry).aig address.val.1 address.val.2).capacitance.value / 2 *
      (current.outputLoadReceiverStateAt downstreamTechnology downstreamGraph address.val.1 address.val.2 time).value ^ 2
  let delta : FiniteEmbodimentChannel → ℝ := fun channel =>
    (outputLoadCapEnergyAt downstreamTechnology downstreamGraph current channel time).value -
      (outputLoadOldCapEnergyAt downstreamTechnology downstreamGraph current channel time).value
  have rows (address : AIGCapacitorAddress (aigOutputBank entry).aig) :
      actual address = old address +
        (outputLoadChannel? hardware clockMax address.val.1 address.val.2).elim 0 delta := by
    cases selected : outputLoadChannel? hardware clockMax address.val.1 address.val.2 with
    | none =>
      dsimp only [actual, old]
      rw [current.outputLoadReceiverStateAt_unloaded _ _ _ _ _ selected]
      simp
    | some channel =>
      have same := (outputLoadChannel?_address_iff hardware clockMax address channel).mp selected
      subst address
      dsimp only [actual, old, delta, Option.elim_some, outputLoadAddress]
      rw [current.outputLoadReceiverStateAt_command]
      change (outputLoadCapEnergyAt downstreamTechnology downstreamGraph current channel time).value =
        (outputLoadOldCapEnergyAt downstreamTechnology downstreamGraph current channel time).value +
        ((outputLoadCapEnergyAt downstreamTechnology downstreamGraph current channel time).value -
          (outputLoadOldCapEnergyAt downstreamTechnology downstreamGraph current channel time).value)
      ring
  have summed := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun address _ => rows address)
  rw [Finset.sum_add_distrib, sum_singleton_lookup (outputLoadAddress hardware clockMax)
    (fun address => outputLoadChannel? hardware clockMax address.val.1 address.val.2)
    (outputLoadChannel?_address_iff hardware clockMax)] at summed
  have recipientRows :
      (∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel time).value) =
      (∑ channel, (outputLoadCapEnergyAt downstreamTechnology downstreamGraph current channel time).value) +
      (drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (current.outputLoadRecipientAt downstreamTechnology downstreamGraph time)).value := by
    dsimp only [drivenRLCBankStoredEnergy]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro channel _
    rfl
  rw [receiverStoredEnergyAt_is_state_projection]
  dsimp only [outputLoadWholeStoredEnergyAt, SIQuantity.add_value, aigActualStoredEnergy, outputLoadInputVoltageAt]
  change _ + (∑ address, actual address) + _ = _ + (∑ address, old address) - _ + _
  dsimp only [delta] at summed
  rw [Finset.sum_sub_distrib] at summed
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
