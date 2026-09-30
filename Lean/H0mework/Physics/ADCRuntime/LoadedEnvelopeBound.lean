import H0mework.Physics.ADCRuntime.LoadedInitialBound

/-! # The existing physical readouts consume the generated loaded-coordinate bound -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Producer Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def loadedReceiverResistorGain (core : ResonantDrivenCoreSource) (channel : FiniteEmbodimentChannel) : ℝ :=
  let run := finiteADCCoreNormalizedRun core
  ((finiteADCCoreDimensionedRun core).seriesResistanceAt channel).value / core.2.voltageScale.value *
    ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) * core.2.currentScale.value)

def loadedReceiverInductorGain (core : ResonantDrivenCoreSource) (channel : FiniteEmbodimentChannel) : ℝ :=
  let run := finiteADCCoreNormalizedRun core
  (((finiteADCCoreDimensionedRun core).seriesResistanceAt channel).value *
      ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) * core.2.currentScale.value) +
    core.2.voltageScale.value) / (resonantInductorOutputScaleAt (finiteADCCorePhysicalSource core) channel).value

theorem loadedReceiverGains_nonneg (core : ResonantDrivenCoreSource) (channel : FiniteEmbodimentChannel) :
    0 ≤ loadedReceiverResistorGain core channel ∧ 0 ≤ loadedReceiverInductorGain core channel := by
  have resistance := (finiteADCSuccessorResistance_pos core channel).le
  have frequency := (compiledFiniteSeriesRLCNetlistRun_frequency_pos (finiteADCCorePhysicalSource core).1 channel).le
  have damping : 0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    rw [show (finiteADCCoreNormalizedRun core).dampingRateAt channel = finiteSeriesRLCDampingRate from
      compiledFiniteSeriesRLCNetlistRun_dampingRateAt _ _]
    exact finiteSeriesRLCDampingRate_pos.le
  have flow := mul_nonneg (add_nonneg frequency damping) core.2.currentScalePositive.le
  exact ⟨mul_nonneg (div_nonneg resistance core.2.voltageScalePositive.le) flow,
    div_nonneg (add_nonneg (mul_nonneg resistance flow) core.2.voltageScalePositive.le)
      (resonantInductorOutputScale_pos (finiteADCCorePhysicalSource core) channel).le⟩

private theorem normalized_envelopes_eq (core : ResonantDrivenCoreSource) (drive : FiniteBinaryDrive)
    (initial : FiniteDimensionedSeriesRLCPortState) (channel : FiniteEmbodimentChannel) :
    let coordinate := drivenHomogeneousCoordinateEnvelopeAt (finiteADCCorePhysicalSource core)
      (sourceOwnedResonantDrivenFrequencyAt core) (sourceOwnedResonantDrivenDriveAt core (binaryDriveState drive)) initial channel
    resonantNormalizedResistorEnvelopeAt core (binaryDriveState drive) initial channel =
      loadedReceiverResistorGain core channel * coordinate ∧
    resonantNormalizedInductorEnvelopeAt core (binaryDriveState drive) initial channel =
      loadedReceiverInductorGain core channel * coordinate := by
  dsimp only [resonantNormalizedResistorEnvelopeAt, resonantNormalizedInductorEnvelopeAt,
    drivenHomogeneousCurrentEnvelopeAt, drivenHomogeneousVoltageEnvelopeAt,
    loadedReceiverResistorGain, loadedReceiverInductorGain, finiteADCCoreDimensionedRun,
    finiteADCCoreNormalizedRun, finiteADCCorePhysicalSource, SIQuantity.scale]
  simp only [SIQuantity.smul_value]
  dsimp only [resonantDrivenCoreDimensionedSource]
  constructor <;> ring

def loadedReceiverEnvelopeBound (core : ResonantDrivenCoreSource) (technology : AIGCellTechnology) : ℝ :=
  Real.sqrt (∑ channel : FiniteEmbodimentChannel,
    ((loadedReceiverResistorGain core channel * loadedReceiverCoordinateEnvelopeBound core technology channel) ^ 2 +
      (loadedReceiverInductorGain core channel * loadedReceiverCoordinateEnvelopeBound core technology channel) ^ 2))

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)

theorem commonRecoveryTarget_legEnvelopes_le (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel) :
    let core := hardware.meteredSource.fixture.coreSource
    let initial := (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
    resonantNormalizedResistorEnvelopeAt core (binaryDriveState drive) initial channel ≤
      loadedReceiverResistorGain core channel * loadedReceiverCoordinateEnvelopeBound core technology channel ∧
    resonantNormalizedInductorEnvelopeAt core (binaryDriveState drive) initial channel ≤
      loadedReceiverInductorGain core channel * loadedReceiverCoordinateEnvelopeBound core technology channel := by
  have coordinate := commonRecoveryTarget_coordinateEnvelope_le downstreamTechnology downstreamGraph current drive channel
  have gains := loadedReceiverGains_nonneg hardware.meteredSource.fixture.coreSource channel
  have exactRead := normalized_envelopes_eq hardware.meteredSource.fixture.coreSource drive
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 channel
  dsimp only at exactRead ⊢
  rw [exactRead.1, exactRead.2]
  exact ⟨mul_le_mul_of_nonneg_left coordinate gains.1, mul_le_mul_of_nonneg_left coordinate gains.2⟩

theorem commonRecoveryTarget_envelope_le (drive : FiniteBinaryDrive) :
    resonantSynchronousEnvelope hardware.meteredSource.fixture.coreSource (binaryDriveState drive)
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 ≤
        loadedReceiverEnvelopeBound hardware.meteredSource.fixture.coreSource technology := by
  unfold resonantSynchronousEnvelope loadedReceiverEnvelopeBound
  apply Real.sqrt_le_sqrt
  unfold resonantSynchronousEnvelopeSq
  apply Finset.sum_le_sum
  intro channel _
  have legs := commonRecoveryTarget_legEnvelopes_le downstreamTechnology downstreamGraph current drive channel
  have gains := loadedReceiverGains_nonneg hardware.meteredSource.fixture.coreSource channel
  have coordinate := loadedReceiverCoordinateEnvelopeBound_nonneg hardware.meteredSource.fixture.coreSource technology channel
  exact add_le_add
    ((sq_le_sq₀ (resonantNormalizedResistorEnvelope_nonneg _ _ _ _) (mul_nonneg gains.1 coordinate)).mpr legs.1)
    ((sq_le_sq₀ (resonantNormalizedInductorEnvelope_nonneg _ _ _ _) (mul_nonneg gains.2 coordinate)).mpr legs.2)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
