import H0mework.Physics.ADCRuntime.SuccessorCoordinates

/-!
# Uniform successor envelope for endpoint-seeded ADC runs

The coordinate bound is converted into resistor and inductor readout bounds,
then summed into the one Hilbert envelope consumed by the uniform-clock layer.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open Netlist.Dissipative.Producer
open Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Physical.Units.Interface

noncomputable section

def finiteADCSuccessorResistorEnvelopeBoundAt
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  let run := finiteADCCoreNormalizedRun core
  let physicalRun := finiteADCCoreDimensionedRun core
  let coordinateBound := finiteADCSuccessorCoordinateEnvelopeBoundAt core channel
  (physicalRun.seriesResistanceAt channel).value /
      core.2.voltageScale.value *
    ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) *
      coordinateBound * core.2.currentScale.value)

def finiteADCSuccessorInductorEnvelopeBoundAt
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  let run := finiteADCCoreNormalizedRun core
  let physicalRun := finiteADCCoreDimensionedRun core
  let coordinateBound := finiteADCSuccessorCoordinateEnvelopeBoundAt core channel
  ((physicalRun.seriesResistanceAt channel).value *
        ((run.baseRun.frequencyAt channel + run.dampingRateAt channel) *
          coordinateBound * core.2.currentScale.value) +
      coordinateBound * core.2.voltageScale.value) /
    (resonantInductorOutputScaleAt
      (finiteADCCorePhysicalSource core) channel).value

theorem finiteADCSuccessorResistorEnvelopeBound_nonneg
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ finiteADCSuccessorResistorEnvelopeBoundAt core channel := by
  unfold finiteADCSuccessorResistorEnvelopeBoundAt
  exact mul_nonneg
    (div_nonneg (finiteADCSuccessorResistance_pos core channel).le
      core.2.voltageScalePositive.le)
    (mul_nonneg
      (mul_nonneg
        (add_nonneg
          (compiledFiniteSeriesRLCNetlistRun_frequency_pos
            (finiteADCCorePhysicalSource core).1 channel).le
          (by
            unfold finiteADCCoreNormalizedRun
            rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
            exact finiteSeriesRLCDampingRate_pos.le))
        (finiteADCSuccessorCoordinateEnvelopeBound_nonneg core channel))
      core.2.currentScalePositive.le)

theorem finiteADCSuccessorInductorEnvelopeBound_nonneg
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ finiteADCSuccessorInductorEnvelopeBoundAt core channel := by
  unfold finiteADCSuccessorInductorEnvelopeBoundAt
  exact div_nonneg
    (add_nonneg
      (mul_nonneg (finiteADCSuccessorResistance_pos core channel).le
        (mul_nonneg
          (mul_nonneg
            (add_nonneg
              (compiledFiniteSeriesRLCNetlistRun_frequency_pos
                (finiteADCCorePhysicalSource core).1 channel).le
              (by
                unfold finiteADCCoreNormalizedRun
                rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
                exact finiteSeriesRLCDampingRate_pos.le))
            (finiteADCSuccessorCoordinateEnvelopeBound_nonneg core channel))
          core.2.currentScalePositive.le))
      (mul_nonneg
        (finiteADCSuccessorCoordinateEnvelopeBound_nonneg core channel)
        core.2.voltageScalePositive.le))
    (resonantInductorOutputScale_pos
      (finiteADCCorePhysicalSource core) channel).le

theorem finiteADCGeneratedEndpoint_nextResistorEnvelope_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) (processingTicks : Nat := 0) :
    let core := source.meteredSource.fixture.coreSource
    resonantNormalizedResistorEnvelopeAt core (binaryDriveState nextDrive)
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks) channel ≤
      finiteADCSuccessorResistorEnvelopeBoundAt core channel := by
  dsimp only
  let core := source.meteredSource.fixture.coreSource
  have coordinateLe := finiteADCGeneratedEndpoint_nextCoordinateEnvelope_le
    source drive nextDrive channel processingTicks
  have resistanceNonnegative :=
    (finiteADCSuccessorResistance_pos core channel).le
  have voltageScalePos := core.2.voltageScalePositive
  have currentScaleNonnegative := core.2.currentScalePositive.le
  have frequencyNonnegative :=
    (compiledFiniteSeriesRLCNetlistRun_frequency_pos
      (finiteADCCorePhysicalSource core).1 channel).le
  have dampingNonnegative :
      0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    unfold finiteADCCoreNormalizedRun
    rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
    exact finiteSeriesRLCDampingRate_pos.le
  unfold resonantNormalizedResistorEnvelopeAt
    drivenHomogeneousCurrentEnvelopeAt
    finiteADCSuccessorResistorEnvelopeBoundAt
  dsimp only
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg resistanceNonnegative voltageScalePos.le)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left coordinateLe
      (add_nonneg frequencyNonnegative dampingNonnegative))
    currentScaleNonnegative

theorem finiteADCGeneratedEndpoint_nextInductorEnvelope_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) (processingTicks : Nat := 0) :
    let core := source.meteredSource.fixture.coreSource
    resonantNormalizedInductorEnvelopeAt core (binaryDriveState nextDrive)
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks) channel ≤
      finiteADCSuccessorInductorEnvelopeBoundAt core channel := by
  dsimp only
  let core := source.meteredSource.fixture.coreSource
  have coordinateLe := finiteADCGeneratedEndpoint_nextCoordinateEnvelope_le
    source drive nextDrive channel processingTicks
  have coordinateNonnegative :=
    finiteSeriesRLCInitialCoordinateEnvelopeAt_nonneg
      (drivenHomogeneousInitialAt
        (finiteADCCorePhysicalSource core)
        (sourceOwnedResonantDrivenFrequencyAt core)
        (sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive))
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks)) channel
  have resistanceNonnegative :=
    (finiteADCSuccessorResistance_pos core channel).le
  have voltageScaleNonnegative := core.2.voltageScalePositive.le
  have currentScaleNonnegative := core.2.currentScalePositive.le
  have frequencyNonnegative :=
    (compiledFiniteSeriesRLCNetlistRun_frequency_pos
      (finiteADCCorePhysicalSource core).1 channel).le
  have dampingNonnegative :
      0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    unfold finiteADCCoreNormalizedRun
    rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
    exact finiteSeriesRLCDampingRate_pos.le
  have denominatorPositive := resonantInductorOutputScale_pos
    (finiteADCCorePhysicalSource core) channel
  unfold resonantNormalizedInductorEnvelopeAt
    drivenHomogeneousCurrentEnvelopeAt drivenHomogeneousVoltageEnvelopeAt
    finiteADCSuccessorInductorEnvelopeBoundAt
  dsimp only
  apply div_le_div_of_nonneg_right _ denominatorPositive.le
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ resistanceNonnegative
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left coordinateLe
        (add_nonneg frequencyNonnegative dampingNonnegative))
      currentScaleNonnegative
  · exact mul_le_mul_of_nonneg_right coordinateLe voltageScaleNonnegative

def finiteADCSuccessorEnvelopeSqBound
    (core : ResonantDrivenCoreSource) : ℝ :=
  ∑ channel : FiniteEmbodimentChannel,
    (finiteADCSuccessorResistorEnvelopeBoundAt core channel ^ 2 +
      finiteADCSuccessorInductorEnvelopeBoundAt core channel ^ 2)

def finiteADCSuccessorEnvelopeBound
    (core : ResonantDrivenCoreSource) : ℝ :=
  Real.sqrt (finiteADCSuccessorEnvelopeSqBound core)

theorem finiteADCGeneratedEndpoint_nextEnvelope_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive) (processingTicks : Nat := 0) :
    let core := source.meteredSource.fixture.coreSource
    resonantSynchronousEnvelope core (binaryDriveState nextDrive)
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks) ≤
      finiteADCSuccessorEnvelopeBound core := by
  dsimp only
  let core := source.meteredSource.fixture.coreSource
  have sumLe :
      resonantSynchronousEnvelopeSq core (binaryDriveState nextDrive)
          (finiteADCGeneratedPhysicalEndpointAt
            source drive processingTicks) ≤
        finiteADCSuccessorEnvelopeSqBound core := by
    unfold resonantSynchronousEnvelopeSq finiteADCSuccessorEnvelopeSqBound
    apply Finset.sum_le_sum
    intro channel _membership
    have resistorLe := finiteADCGeneratedEndpoint_nextResistorEnvelope_le
      source drive nextDrive channel processingTicks
    have inductorLe := finiteADCGeneratedEndpoint_nextInductorEnvelope_le
      source drive nextDrive channel processingTicks
    have resistorNonnegative := resonantNormalizedResistorEnvelope_nonneg
      core (binaryDriveState nextDrive)
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks) channel
    have inductorNonnegative := resonantNormalizedInductorEnvelope_nonneg
      core (binaryDriveState nextDrive)
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks) channel
    have resistorBoundNonnegative :=
      finiteADCSuccessorResistorEnvelopeBound_nonneg core channel
    have inductorBoundNonnegative :=
      finiteADCSuccessorInductorEnvelopeBound_nonneg core channel
    exact add_le_add
      ((sq_le_sq₀ resistorNonnegative resistorBoundNonnegative).mpr resistorLe)
      ((sq_le_sq₀ inductorNonnegative inductorBoundNonnegative).mpr inductorLe)
  unfold resonantSynchronousEnvelope finiteADCSuccessorEnvelopeBound
  exact Real.sqrt_le_sqrt sumLe

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
