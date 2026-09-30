import H0mework.Physics.ReceiverActuation.OutputEnergyEnvelope
import H0mework.Physics.ReceiverActuation.CommonTarget

/-! # Source-only coordinates for the actual loaded and recovered recipient -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Producer Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def loadedReceiverInitialVoltageBound (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) : ℝ :=
  Real.sqrt ((wholeReceiverOutputEnergyEnvelopeAt core technology channel).value /
    ((finiteADCCoreDimensionedRun core).capacitanceAt channel).value)

def loadedReceiverInitialCurrentBound (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) : ℝ :=
  Real.sqrt ((wholeReceiverOutputEnergyEnvelopeAt core technology channel).value /
    ((finiteADCCoreDimensionedRun core).inductanceAt channel).value)

def loadedReceiverVoltageResidualBound (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) : ℝ :=
  loadedReceiverInitialVoltageBound core technology channel / core.2.voltageScale.value +
    finiteADCSuccessorInductorRatioAt core channel

def loadedReceiverCurrentResidualBound (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) : ℝ :=
  loadedReceiverInitialCurrentBound core technology channel / core.2.currentScale.value +
    finiteADCSuccessorPeriodicCurrentRatioBoundAt core channel

def loadedReceiverCoordinateEnvelopeBound (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) : ℝ :=
  let run := finiteADCCoreNormalizedRun core
  (loadedReceiverCurrentResidualBound core technology channel + run.dampingRateAt channel *
      loadedReceiverVoltageResidualBound core technology channel) / run.baseRun.frequencyAt channel +
    loadedReceiverVoltageResidualBound core technology channel

theorem loadedReceiverCoordinateEnvelopeBound_nonneg (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) :
    0 ≤ loadedReceiverCoordinateEnvelopeBound core technology channel := by
  have voltage := core.2.voltageScalePositive.le
  have current := core.2.currentScalePositive.le
  have frequency := (compiledFiniteSeriesRLCNetlistRun_frequency_pos (finiteADCCorePhysicalSource core).1 channel).le
  have damping : 0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    rw [show (finiteADCCoreNormalizedRun core).dampingRateAt channel = finiteSeriesRLCDampingRate from
      compiledFiniteSeriesRLCNetlistRun_dampingRateAt _ _]
    exact finiteSeriesRLCDampingRate_pos.le
  have voltageResidual : 0 ≤ loadedReceiverVoltageResidualBound core technology channel :=
    add_nonneg (div_nonneg (Real.sqrt_nonneg _) voltage) (finiteADCSuccessorInductorRatio_pos core channel).le
  have currentResidual : 0 ≤ loadedReceiverCurrentResidualBound core technology channel :=
    add_nonneg (div_nonneg (Real.sqrt_nonneg _) current) (finiteADCSuccessorPeriodicCurrentRatioBound_pos core channel).le
  exact add_nonneg (div_nonneg (add_nonneg currentResidual (mul_nonneg damping voltageResidual)) frequency) voltageResidual

private theorem absolute_of_half_energy {capacitance inductance voltage current energy : ℝ}
    (capPositive : 0 < capacitance) (indPositive : 0 < inductance)
    (bounded : capacitance / 2 * voltage ^ 2 + inductance / 2 * current ^ 2 ≤ energy / 2) :
    |voltage| ≤ Real.sqrt (energy / capacitance) ∧ |current| ≤ Real.sqrt (energy / inductance) := by
  constructor
  · apply Real.abs_le_sqrt
    apply (le_div_iff₀ capPositive).mpr
    nlinarith [mul_nonneg indPositive.le (sq_nonneg current)]
  · apply Real.abs_le_sqrt
    apply (le_div_iff₀ indPositive).mpr
    nlinarith [mul_nonneg capPositive.le (sq_nonneg voltage)]

private theorem normalized_residual_bound {value periodic scale valueBound periodicBound : ℝ}
    (scalePositive : 0 < scale) (bounded : |value| ≤ valueBound)
    (periodicBounded : |periodic / scale| ≤ periodicBound) :
    |(value - periodic) / scale| ≤ valueBound / scale + periodicBound := by
  rw [sub_div]
  apply (abs_sub _ _).trans
  rw [abs_div, abs_of_pos scalePositive]
  exact add_le_add (div_le_div_of_nonneg_right bounded scalePositive.le) periodicBounded

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)

theorem commonRecoveryTarget_recipientEnergy_le_source (channel : FiniteEmbodimentChannel) :
    let core := hardware.meteredSource.fixture.coreSource
    let run := finiteADCCoreDimensionedRun core
    let initial := (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
    (run.capacitanceAt channel).value / 2 * (initial.voltageAt channel).value ^ 2 +
      (run.inductanceAt channel).value / 2 * (initial.currentAt channel).value ^ 2 ≤
        (wholeReceiverOutputEnergyEnvelopeAt core technology channel).value / 2 := by
  have recipient := commonRecipientRecoveryEnergyAt_le_original_half downstreamTechnology downstreamGraph current channel
    (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value
    (commonRecoverySampleTime_nonnegative downstreamTechnology downstreamGraph current)
  rw [commonRecipientRecoveryEnergyAt_eq_physical] at recipient
  exact recipient.trans (div_le_div_of_nonneg_right
    (current.outputLoadEnergyAt_initial_le_source_envelope downstreamTechnology downstreamGraph channel) (by norm_num))

theorem commonRecoveryTarget_initial_absolute_bounds (channel : FiniteEmbodimentChannel) :
    let core := hardware.meteredSource.fixture.coreSource
    let initial := (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
    |(initial.voltageAt channel).value| ≤ loadedReceiverInitialVoltageBound core technology channel ∧
    |(initial.currentAt channel).value| ≤ loadedReceiverInitialCurrentBound core technology channel :=
  absolute_of_half_energy (compiledFiniteDimensionedSeriesRLC_capacitance_pos _ channel)
    (compiledFiniteDimensionedSeriesRLC_inductance_pos _ channel)
    (commonRecoveryTarget_recipientEnergy_le_source downstreamTechnology downstreamGraph current channel)

theorem commonRecoveryTarget_residual_bounds (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel) :
    let core := hardware.meteredSource.fixture.coreSource
    let initial := (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
    |drivenInitialVoltageResidualRatioAt (finiteADCCorePhysicalSource core)
      (sourceOwnedResonantDrivenFrequencyAt core) (sourceOwnedResonantDrivenDriveAt core (binaryDriveState drive))
      initial channel| ≤ loadedReceiverVoltageResidualBound core technology channel ∧
    |drivenInitialCurrentResidualRatioAt (finiteADCCorePhysicalSource core)
      (sourceOwnedResonantDrivenFrequencyAt core) (sourceOwnedResonantDrivenDriveAt core (binaryDriveState drive))
      initial channel| ≤ loadedReceiverCurrentResidualBound core technology channel := by
  have initial := commonRecoveryTarget_initial_absolute_bounds downstreamTechnology downstreamGraph current channel
  exact ⟨normalized_residual_bound hardware.meteredSource.fixture.coreSource.2.voltageScalePositive initial.1
      (resonantPeriodicBinaryDriveCapacitor_normalized_abs_le hardware.meteredSource.fixture.coreSource drive channel 0),
    normalized_residual_bound hardware.meteredSource.fixture.coreSource.2.currentScalePositive initial.2
      (resonantPeriodicBinaryDriveCurrent_normalized_abs_le hardware.meteredSource.fixture.coreSource drive channel 0)⟩

theorem commonRecoveryTarget_coordinateEnvelope_le (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel) :
    let core := hardware.meteredSource.fixture.coreSource
    drivenHomogeneousCoordinateEnvelopeAt (finiteADCCorePhysicalSource core)
      (sourceOwnedResonantDrivenFrequencyAt core) (sourceOwnedResonantDrivenDriveAt core (binaryDriveState drive))
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 channel ≤
        loadedReceiverCoordinateEnvelopeBound core technology channel := by
  let core := hardware.meteredSource.fixture.coreSource
  have residual := commonRecoveryTarget_residual_bounds downstreamTechnology downstreamGraph current drive channel
  have frequency := (compiledFiniteSeriesRLCNetlistRun_frequency_pos (finiteADCCorePhysicalSource core).1 channel).le
  have damping : 0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    rw [show (finiteADCCoreNormalizedRun core).dampingRateAt channel = finiteSeriesRLCDampingRate from
      compiledFiniteSeriesRLCNetlistRun_dampingRateAt _ _]
    exact finiteSeriesRLCDampingRate_pos.le
  dsimp only
  unfold drivenHomogeneousCoordinateEnvelopeAt finiteSeriesRLCInitialCoordinateEnvelopeAt drivenHomogeneousInitialAt
  dsimp only [sourcePort, targetPort]
  rw [abs_div, abs_of_nonneg frequency]
  apply le_trans (add_le_add (div_le_div_of_nonneg_right (abs_add_le _ _) frequency) le_rfl)
  dsimp only [finiteADCCoreNormalizedRun] at damping
  rw [abs_mul, abs_of_nonneg damping]
  exact add_le_add (div_le_div_of_nonneg_right
    (add_le_add residual.2 (mul_le_mul_of_nonneg_left residual.1 damping)) frequency) residual.1

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
