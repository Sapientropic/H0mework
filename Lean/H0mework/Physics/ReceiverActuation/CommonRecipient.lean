import H0mework.Physics.ReceiverActuation.CommonLoad
import H0mework.Physics.RLCResponse.PortState

/-! # All recipient rows continue together from the same actual common load endpoint -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Producer Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

private def commonRecipientNormalizedSeed : FiniteEmbodimentState :=
  normalizeFiniteDimensionedSeriesRLCPortState
    (compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource))
    (commonOutputLoadRecipient downstreamTechnology downstreamGraph current)

def commonRecipientRecoveryAt (time : ℝ) : FiniteDimensionedSeriesRLCPortState where
  voltageAt channel := finiteDimensionedSeriesRLCVoltageAt
    (compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource))
    (commonRecipientNormalizedSeed downstreamTechnology downstreamGraph current) channel ⟨time⟩
  currentAt channel := finiteDimensionedSeriesRLCCurrentAt
    (compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource))
    (commonRecipientNormalizedSeed downstreamTechnology downstreamGraph current) channel ⟨time⟩

theorem commonRecipientRecoveryAt_initial :
    commonRecipientRecoveryAt downstreamTechnology downstreamGraph current 0 =
      commonOutputLoadRecipient downstreamTechnology downstreamGraph current := by
  have initial := compiledFiniteDimensionedSeriesRLC_portStateOfNormalized_normalize
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (commonOutputLoadRecipient downstreamTechnology downstreamGraph current)
  simpa only [commonRecipientRecoveryAt, commonRecipientNormalizedSeed,
    finiteDimensionedSeriesRLCVoltageAt, finiteSeriesRLCVoltageAt, finiteDimensionedSeriesRLCCurrentAt,
    finiteSeriesRLCCurrentAt, finiteDimensionedSeriesRLCNormalizedTimeAt, SIQuantity.sameDimensionRatio_value,
    zero_div, finiteSeriesRLCFlowAt_zero, finiteDimensionedSeriesRLCPortStateOfNormalized,
    finiteDimensionedSeriesRLCStateOfNormalized] using initial

def commonRecipientRecoveryEnergyAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIJoule :=
  (1 / 2 : ℝ) • finiteDimensionedSeriesRLCEnergyAt
    (compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource))
    (commonRecipientNormalizedSeed downstreamTechnology downstreamGraph current) channel ⟨time⟩

theorem commonRecipientRecoveryEnergyAt_eq_physical (channel : FiniteEmbodimentChannel) (time : ℝ) :
    let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    let state := commonRecipientRecoveryAt downstreamTechnology downstreamGraph current time
    (commonRecipientRecoveryEnergyAt downstreamTechnology downstreamGraph current channel time).value =
      (run.capacitanceAt channel).value / 2 * (state.voltageAt channel).value ^ 2 +
      (run.inductanceAt channel).value / 2 * (state.currentAt channel).value ^ 2 := by
  simp only [commonRecipientRecoveryEnergyAt, commonRecipientRecoveryAt, finiteDimensionedSeriesRLCEnergyAt,
    SIQuantity.smul_value, SIQuantity.add_value, inductiveEnergy_value, capacitiveEnergy_value]
  ring

theorem commonRecipientRecoveryEnergyAt_initial (channel : FiniteEmbodimentChannel) :
    let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
    let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode
    let original := current.outputLoadInitialRecipient downstreamTechnology downstreamGraph
    commonRecipientRecoveryEnergyAt downstreamTechnology downstreamGraph current channel 0 =
      capacitorRLCRecipientEnergyAt cell hold (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        channel (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
        (original.voltageAt channel) (original.currentAt channel)
        (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value := by
  dsimp only
  apply SIQuantity.ext
  rw [commonRecipientRecoveryEnergyAt_eq_physical, commonRecipientRecoveryAt_initial]
  rfl

theorem commonRecipientRecoveryEnergyAt_antitone (channel : FiniteEmbodimentChannel) :
    Antitone (fun t => (commonRecipientRecoveryEnergyAt downstreamTechnology downstreamGraph current channel t).value) := by
  intro earlier later ordered
  exact mul_le_mul_of_nonneg_left
    (compiledFiniteDimensionedSeriesRLC_energy_antitone
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
      (commonRecipientNormalizedSeed downstreamTechnology downstreamGraph current) channel ordered)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem commonRecipientRecoveryEnergyAt_le_original_half (channel : FiniteEmbodimentChannel)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    (commonRecipientRecoveryEnergyAt downstreamTechnology downstreamGraph current channel time).value ≤
      (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value / 2 := by
  have still := commonRecipientRecoveryEnergyAt_antitone downstreamTechnology downstreamGraph current channel nonnegative
  dsimp only at still
  have loadBound := commonOutputLoadEnergy_le_half downstreamTechnology downstreamGraph current channel
  have holdNonnegative : 0 ≤
      (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel).capacitance.value / 2 *
        current.outputLoadStateAt downstreamTechnology downstreamGraph channel
          (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
            downstreamTechnology downstreamGraph).value 0 ^ 2 :=
    mul_nonneg (div_nonneg (outputLoadCell (hardware := hardware) (clockMax := clockMax)
      (technology := technology) channel).capacitance_pos.le (by norm_num)) (sq_nonneg _)
  rw [commonRecipientRecoveryEnergyAt_initial] at still
  dsimp only [outputLoadEnergyAt, capacitorRLCEnergyAt, capacitorRLCHoldEnergyAt, SIQuantity.add_value] at loadBound ⊢
  dsimp only [outputLoadStateAt, capacitorRLCHoldEnergyAt] at holdNonnegative
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
