import H0mework.Physics.DrivenEnergy.RLCWork
import H0mework.Physics.ADCRuntime.ProcessingTime

/-!
# Complete driven-recipient bank and actual ADC-current work

Every registered recipient channel is counted once. The finite bank sums the actual branch
powers before integrating, and the runtime consumer reads the existing generated physical
state throughout the sample-to-switch wait. No supply or heat is inferred from endpoint loss.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface MeasureTheory
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def drivenRLCBankStoredEnergy (source : DimensionedSeriesRLCSource)
    (state : FiniteDimensionedSeriesRLCPortState) : SIJoule :=
  ⟨∑ channel, (drivenRLCStoredEnergy source state channel).value⟩

variable (source : DimensionedSeriesRLCSource)
  (frequencyAt : FiniteEmbodimentChannel → SIHertz)
  (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)
  (initial : FiniteDimensionedSeriesRLCPortState)

def drivenRLCBankEnergyAt (time : ℝ) : SIJoule :=
  drivenRLCBankStoredEnergy source (drivenTotalPortStateAt source frequencyAt driveAt initial ⟨time⟩)

def drivenRLCBankSourcePowerAt (time : ℝ) : SIWatt :=
  ⟨∑ channel, (drivenRLCSourcePowerAt source frequencyAt driveAt initial channel time).value⟩

def drivenRLCBankHeatPowerAt (time : ℝ) : SIWatt :=
  ⟨∑ channel, (drivenRLCHeatPowerAt source frequencyAt driveAt initial channel time).value⟩

theorem drivenRLCBankStoredEnergy_nonneg (state : FiniteDimensionedSeriesRLCPortState) :
    0 ≤ (drivenRLCBankStoredEnergy source state).value :=
  Finset.sum_nonneg (s := Finset.univ) fun channel _ => drivenRLCStoredEnergy_nonneg source channel state

theorem drivenRLCBankHeatPowerAt_nonneg (time : ℝ) :
    0 ≤ (drivenRLCBankHeatPowerAt source frequencyAt driveAt initial time).value :=
  Finset.sum_nonneg (s := Finset.univ) fun channel _ =>
    drivenRLCHeatPowerAt_nonneg source frequencyAt driveAt initial channel time

theorem drivenRLCBankEnergyAt_power_balance
    (frequencyPositive : ∀ channel, 0 < (frequencyAt channel).value) (time : ℝ) :
    HasDerivAt (fun t => (drivenRLCBankEnergyAt source frequencyAt driveAt initial t).value)
      ((drivenRLCBankSourcePowerAt source frequencyAt driveAt initial time).value -
        (drivenRLCBankHeatPowerAt source frequencyAt driveAt initial time).value) time := by
  have channels := HasDerivAt.fun_sum (u := Finset.univ)
    (fun channel (_ : channel ∈ (Finset.univ : Finset FiniteEmbodimentChannel)) =>
      drivenRLCEnergyAt_power_balance source frequencyAt driveAt initial channel frequencyPositive time)
  convert channels using 1 <;> first | rfl | (
    dsimp only [drivenRLCBankSourcePowerAt, drivenRLCBankHeatPowerAt]
    rw [Finset.sum_sub_distrib])

theorem drivenRLCBankPowers_continuous :
    Continuous (fun t => (drivenRLCBankSourcePowerAt source frequencyAt driveAt initial t).value) ∧
    Continuous (fun t => (drivenRLCBankHeatPowerAt source frequencyAt driveAt initial t).value) :=
  ⟨continuous_finsetSum Finset.univ (fun channel _ =>
      (drivenRLCPowers_continuous source frequencyAt driveAt initial channel).1),
    continuous_finsetSum Finset.univ (fun channel _ =>
      (drivenRLCPowers_continuous source frequencyAt driveAt initial channel).2)⟩

def drivenRLCBankWork (start stop : SISecond) : SIJoule :=
  ⟨∫ t in start.value..stop.value, (drivenRLCBankSourcePowerAt source frequencyAt driveAt initial t).value⟩

def drivenRLCBankHeat (start stop : SISecond) : SIJoule :=
  ⟨∫ t in start.value..stop.value, (drivenRLCBankHeatPowerAt source frequencyAt driveAt initial t).value⟩

theorem drivenRLCBankHeat_nonneg (start stop : SISecond) (ordered : start.value ≤ stop.value) :
    0 ≤ (drivenRLCBankHeat source frequencyAt driveAt initial start stop).value :=
  intervalIntegral.integral_nonneg_of_forall ordered
    (fun t => drivenRLCBankHeatPowerAt_nonneg source frequencyAt driveAt initial t)

theorem drivenRLCBankEnergyAt_integrated_balance
    (frequencyPositive : ∀ channel, 0 < (frequencyAt channel).value) (start stop : SISecond) :
    (drivenRLCBankEnergyAt source frequencyAt driveAt initial stop.value).value -
      (drivenRLCBankEnergyAt source frequencyAt driveAt initial start.value).value =
        (drivenRLCBankWork source frequencyAt driveAt initial start stop).value -
          (drivenRLCBankHeat source frequencyAt driveAt initial start stop).value := by
  obtain ⟨sourceContinuous, heatContinuous⟩ :=
    drivenRLCBankPowers_continuous source frequencyAt driveAt initial
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc start.value stop.value) =>
      drivenRLCBankEnergyAt_power_balance source frequencyAt driveAt initial frequencyPositive t)
    ((sourceContinuous.sub heatContinuous).intervalIntegrable start.value stop.value)
  rw [intervalIntegral.integral_sub (sourceContinuous.intervalIntegrable start.value stop.value)
    (heatContinuous.intervalIntegrable start.value stop.value)] at paid
  exact paid.symm

section ActualCurrent

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  (current : FiniteADCPhysicalRuntimeCurrent hardware)

/-- Storage reads the runtime's actual `(V,I)`, not its periodic target or decoded bit. -/
def finiteADCRecipientStoredEnergyAt (time : SISecond) : SIJoule :=
  drivenRLCBankStoredEnergy
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (finiteADCPhysicalStateAt current time)

def finiteADCRecipientWork (start stop : SISecond) : SIJoule :=
  drivenRLCBankWork
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenDriveAt hardware.meteredSource.fixture.coreSource
      (binaryDriveState current.val.drive)) current.val.initial start stop

def finiteADCRecipientHeat (start stop : SISecond) : SIJoule :=
  drivenRLCBankHeat
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenDriveAt hardware.meteredSource.fixture.coreSource
      (binaryDriveState current.val.drive)) current.val.initial start stop

/-- The exact stored run, its physical initial state and actual driving source share one bill. -/
theorem finiteADCRecipientStoredEnergyAt_integrated_balance (start stop : SISecond) :
    (finiteADCRecipientStoredEnergyAt current stop).value -
      (finiteADCRecipientStoredEnergyAt current start).value =
        (finiteADCRecipientWork current start stop).value -
          (finiteADCRecipientHeat current start stop).value := by
  unfold finiteADCRecipientStoredEnergyAt
  rw [finiteADCPhysicalStateAt_commutes, finiteADCPhysicalStateAt_commutes]
  exact drivenRLCBankEnergyAt_integrated_balance _ _ _ _
    (sourceOwnedResonantDrivenFrequencyAt_positive hardware.meteredSource.fixture.coreSource) start stop

theorem finiteADCRecipientHeat_nonneg (start stop : SISecond) (ordered : start.value ≤ stop.value) :
    0 ≤ (finiteADCRecipientHeat current start stop).value :=
  drivenRLCBankHeat_nonneg _ _ _ _ start stop ordered

/-- Waiting for the receiver remains an actual driven-recipient interval, with its own heat. -/
theorem finiteADCRecipient_sample_to_switch_paid (processingTicks : Nat) :
    (finiteADCRecipientStoredEnergyAt current (finiteADCPhysicalSwitchTimeAt current processingTicks)).value -
      (finiteADCRecipientStoredEnergyAt current current.val.executedDuration).value =
        (finiteADCRecipientWork current current.val.executedDuration
          (finiteADCPhysicalSwitchTimeAt current processingTicks)).value -
        (finiteADCRecipientHeat current current.val.executedDuration
          (finiteADCPhysicalSwitchTimeAt current processingTicks)).value :=
  finiteADCRecipientStoredEnergyAt_integrated_balance current _ _

theorem finiteADCRecipient_sample_to_switch_heat_nonneg (processingTicks : Nat) :
    0 ≤ (finiteADCRecipientHeat current current.val.executedDuration
      (finiteADCPhysicalSwitchTimeAt current processingTicks)).value :=
  finiteADCRecipientHeat_nonneg current _ _ (finiteADCPhysicalSwitchTimeAt_ge_sample current processingTicks)

end ActualCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
