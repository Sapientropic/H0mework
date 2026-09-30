import H0mework.Physics.Measurement.Demodulation
import H0mework.Physics.PortCoupling.AdditiveTolerance

/-!
# Quantitative finite settling of the synchronous RLC readout

The exact synchronous demodulator is combined with the source-generated
transient envelopes.  Orthogonality yields the ten-channel L2 budget, from
which the compiler calculates a positive finite duration and an additive
disturbance strictly below the existing coupling threshold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section


/-! ## Orthogonal demodulation and the exact ten-port envelope -/

def resonantSynchronousStateErrorAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond) : FiniteEmbodimentState :=
  resonantActualSynchronousStateAt source input initial physicalTime -
    resonantPeriodicSynchronousStateAt source input physicalTime

theorem resonantSynchronousStateError_channelEnergy_eq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    channelEnergy
        (resonantSynchronousStateErrorAt
          source input initial physicalTime) channel =
      resonantNormalizedResistorErrorAt
          source input initial channel physicalTime ^ 2 +
        resonantNormalizedInductorErrorAt
          source input initial channel physicalTime ^ 2 := by
  let phase := resonantSynchronousPhaseAt source channel physicalTime
  let resistorError := resonantNormalizedResistorErrorAt
    source input initial channel physicalTime
  let inductorError := resonantNormalizedInductorErrorAt
    source input initial channel physicalTime
  have circle := Real.sin_sq_add_cos_sq phase
  have sourceErrorEq :
      sourcePort (resonantSynchronousStateErrorAt
        source input initial physicalTime) channel =
        Real.sin phase * inductorError -
          Real.cos phase * resistorError := by
    simp [sourcePort, resonantSynchronousStateErrorAt,
      resonantActualSynchronousStateAt, resonantPeriodicSynchronousStateAt,
      synchronousDemodulatedPortAt, phase, resistorError, inductorError,
      resonantNormalizedResistorErrorAt,
      resonantNormalizedInductorErrorAt]
    ring
  have targetErrorEq :
      targetPort (resonantSynchronousStateErrorAt
        source input initial physicalTime) channel =
        Real.cos phase * inductorError +
          Real.sin phase * resistorError := by
    simp [targetPort, resonantSynchronousStateErrorAt,
      resonantActualSynchronousStateAt, resonantPeriodicSynchronousStateAt,
      synchronousDemodulatedPortAt, phase, resistorError, inductorError,
      resonantNormalizedResistorErrorAt,
      resonantNormalizedInductorErrorAt]
    ring
  rw [channelEnergy, sourceErrorEq, targetErrorEq]
  change
    (Real.sin phase * inductorError - Real.cos phase * resistorError) ^ 2 +
      (Real.cos phase * inductorError + Real.sin phase * resistorError) ^ 2 =
        resistorError ^ 2 + inductorError ^ 2
  calc
    _ = (Real.sin phase ^ 2 + Real.cos phase ^ 2) *
          (resistorError ^ 2 + inductorError ^ 2) := by ring
    _ = _ := by rw [circle]; ring

def resonantSynchronousDecayAt
    (source : ResonantDrivenCoreSource) (physicalTime : SISecond) : ℝ :=
  Real.exp
    (-drivenCommonPhysicalDampingRate
        (resonantDrivenCoreDimensionedSource source) * physicalTime.value)

theorem resonantSynchronousDecay_pos
    (source : ResonantDrivenCoreSource) (physicalTime : SISecond) :
    0 < resonantSynchronousDecayAt source physicalTime :=
  Real.exp_pos _

def resonantSynchronousEnvelopeSq
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) : ℝ :=
  ∑ channel : FiniteEmbodimentChannel,
    (resonantNormalizedResistorEnvelopeAt source input initial channel ^ 2 +
      resonantNormalizedInductorEnvelopeAt source input initial channel ^ 2)

theorem resonantSynchronousEnvelopeSq_nonneg
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    0 ≤ resonantSynchronousEnvelopeSq source input initial := by
  unfold resonantSynchronousEnvelopeSq
  exact Finset.sum_nonneg fun channel _ =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)

def resonantSynchronousEnvelope
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) : ℝ :=
  Real.sqrt (resonantSynchronousEnvelopeSq source input initial)

theorem resonantSynchronousEnvelope_nonneg
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    0 ≤ resonantSynchronousEnvelope source input initial :=
  Real.sqrt_nonneg _

theorem resonantSynchronousStateError_channelEnergy_le
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (channel : FiniteEmbodimentChannel) (physicalTime : SISecond) :
    channelEnergy
        (resonantSynchronousStateErrorAt
          source input initial physicalTime) channel ≤
      resonantSynchronousDecayAt source physicalTime ^ 2 *
        (resonantNormalizedResistorEnvelopeAt
            source input initial channel ^ 2 +
          resonantNormalizedInductorEnvelopeAt
            source input initial channel ^ 2) := by
  rw [resonantSynchronousStateError_channelEnergy_eq]
  have resistorBound := resonantNormalizedResistorError_abs_le
    source input initial channel physicalTime
  have inductorBound := resonantNormalizedInductorError_abs_le
    source input initial channel physicalTime
  rw [drivenHomogeneousDecayAt_eq_commonExponential] at resistorBound inductorBound
  change
    |resonantNormalizedResistorErrorAt
        source input initial channel physicalTime| ≤
      resonantSynchronousDecayAt source physicalTime *
        resonantNormalizedResistorEnvelopeAt source input initial channel
      at resistorBound
  change
    |resonantNormalizedInductorErrorAt
        source input initial channel physicalTime| ≤
      resonantSynchronousDecayAt source physicalTime *
        resonantNormalizedInductorEnvelopeAt source input initial channel
      at inductorBound
  have resistorRightNonneg :
      0 ≤ resonantSynchronousDecayAt source physicalTime *
        resonantNormalizedResistorEnvelopeAt source input initial channel :=
    mul_nonneg (resonantSynchronousDecay_pos source physicalTime).le
      (resonantNormalizedResistorEnvelope_nonneg
        source input initial channel)
  have inductorRightNonneg :
      0 ≤ resonantSynchronousDecayAt source physicalTime *
        resonantNormalizedInductorEnvelopeAt source input initial channel :=
    mul_nonneg (resonantSynchronousDecay_pos source physicalTime).le
      (resonantNormalizedInductorEnvelope_nonneg
        source input initial channel)
  have resistorSq :
      resonantNormalizedResistorErrorAt
          source input initial channel physicalTime ^ 2 ≤
        (resonantSynchronousDecayAt source physicalTime *
          resonantNormalizedResistorEnvelopeAt
            source input initial channel) ^ 2 := by
    apply (sq_le_sq).2
    rw [abs_of_nonneg resistorRightNonneg]
    exact resistorBound
  have inductorSq :
      resonantNormalizedInductorErrorAt
          source input initial channel physicalTime ^ 2 ≤
        (resonantSynchronousDecayAt source physicalTime *
          resonantNormalizedInductorEnvelopeAt
            source input initial channel) ^ 2 := by
    apply (sq_le_sq).2
    rw [abs_of_nonneg inductorRightNonneg]
    exact inductorBound
  calc
    _ ≤ (resonantSynchronousDecayAt source physicalTime *
          resonantNormalizedResistorEnvelopeAt
            source input initial channel) ^ 2 +
        (resonantSynchronousDecayAt source physicalTime *
          resonantNormalizedInductorEnvelopeAt
            source input initial channel) ^ 2 :=
      add_le_add resistorSq inductorSq
    _ = _ := by ring

theorem resonantSynchronousStateError_energy_le
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond) :
    energy (resonantSynchronousStateErrorAt
        source input initial physicalTime) ≤
      resonantSynchronousDecayAt source physicalTime ^ 2 *
        resonantSynchronousEnvelopeSq source input initial := by
  unfold energy resonantSynchronousEnvelopeSq
  calc
    ∑ channel : FiniteEmbodimentChannel,
        channelEnergy
          (resonantSynchronousStateErrorAt
            source input initial physicalTime) channel ≤
      ∑ channel : FiniteEmbodimentChannel,
        resonantSynchronousDecayAt source physicalTime ^ 2 *
          (resonantNormalizedResistorEnvelopeAt
              source input initial channel ^ 2 +
            resonantNormalizedInductorEnvelopeAt
              source input initial channel ^ 2) := by
        exact Finset.sum_le_sum fun channel _ =>
          resonantSynchronousStateError_channelEnergy_le
            source input initial channel physicalTime
    _ = _ := by rw [Finset.mul_sum]

theorem resonantSynchronousStateError_hilbertNorm_le
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond) :
    ‖encodeHilbert (resonantSynchronousStateErrorAt
        source input initial physicalTime)‖ ≤
      resonantSynchronousDecayAt source physicalTime *
        resonantSynchronousEnvelope source input initial := by
  have energyBound := resonantSynchronousStateError_energy_le
    source input initial physicalTime
  rw [energy_eq_encodeHilbert_norm_sq] at energyBound
  have envelopeSquare := Real.sq_sqrt
    (resonantSynchronousEnvelopeSq_nonneg source input initial)
  have squareBound :
      ‖encodeHilbert (resonantSynchronousStateErrorAt
          source input initial physicalTime)‖ ^ 2 ≤
        (resonantSynchronousDecayAt source physicalTime *
          resonantSynchronousEnvelope source input initial) ^ 2 := by
    calc
      _ ≤ resonantSynchronousDecayAt source physicalTime ^ 2 *
          resonantSynchronousEnvelopeSq source input initial := energyBound
      _ = _ := by
        unfold resonantSynchronousEnvelope
        calc
          resonantSynchronousDecayAt source physicalTime ^ 2 *
              resonantSynchronousEnvelopeSq source input initial =
            resonantSynchronousDecayAt source physicalTime ^ 2 *
              Real.sqrt
                (resonantSynchronousEnvelopeSq source input initial) ^ 2 := by
                  rw [envelopeSquare]
          _ = _ := by ring
  exact (sq_le_sq₀
    (norm_nonneg _)
    (mul_nonneg (resonantSynchronousDecay_pos source physicalTime).le
      (resonantSynchronousEnvelope_nonneg source input initial))).mp squareBound

def resonantActualSynchronousHilbertOutputAt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond) : HilbertEmbodimentState :=
  encodeHilbert
    (resonantActualSynchronousStateAt source input initial physicalTime)

theorem resonantActualSynchronousHilbertError_eq_stateError
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond) :
    resonantActualSynchronousHilbertOutputAt
        source input initial physicalTime -
      idealQuarterOperator (encodeHilbert input) =
    encodeHilbert (resonantSynchronousStateErrorAt
      source input initial physicalTime) := by
  rw [idealQuarterOperator_apply]
  rw [← resonantPeriodicSynchronousState_eq_idealQuarter
    source input physicalTime]
  change encodeHilbert
      (resonantActualSynchronousStateAt source input initial physicalTime) -
    encodeHilbert (resonantPeriodicSynchronousStateAt
      source input physicalTime) = _
  rw [← complexHilbertPortEquiv_apply,
    ← complexHilbertPortEquiv_apply,
    ← complexHilbertPortEquiv_apply,
    ← map_sub]
  rfl

def resonantSynchronousSettlingDurationFor
    (errorTolerance : ℝ)
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) : SISecond :=
  ⟨positiveExponentialSettlingTime
    (drivenCommonPhysicalDampingRate
      (resonantDrivenCoreDimensionedSource source))
    (resonantSynchronousEnvelope source input initial)
    errorTolerance⟩

theorem resonantSynchronousSettlingDurationFor_pos
    (errorTolerance : ℝ) (errorTolerancePositive : 0 < errorTolerance)
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    0 < (resonantSynchronousSettlingDurationFor errorTolerance
      source input initial).value :=
  positiveExponentialSettlingTime_pos
    (drivenCommonPhysicalDampingRate_pos
      (resonantDrivenCoreDimensionedSource source))
    (resonantSynchronousEnvelope_nonneg source input initial)
    errorTolerancePositive

theorem resonantSynchronous_afterGeneratedDurationFor_error_lt
    (errorTolerance : ℝ) (errorTolerancePositive : 0 < errorTolerance)
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond)
    (afterGenerated :
      (resonantSynchronousSettlingDurationFor errorTolerance
        source input initial).value ≤ physicalTime.value) :
    ‖resonantActualSynchronousHilbertOutputAt
          source input initial physicalTime -
        idealQuarterOperator (encodeHilbert input)‖ < errorTolerance := by
  rw [resonantActualSynchronousHilbertError_eq_stateError]
  apply lt_of_le_of_lt
    (resonantSynchronousStateError_hilbertNorm_le
      source input initial physicalTime)
  have settles := positiveExponentialEnvelope_settles
    (drivenCommonPhysicalDampingRate_pos
      (resonantDrivenCoreDimensionedSource source))
    errorTolerancePositive afterGenerated
  simpa [resonantSynchronousSettlingDurationFor,
    resonantSynchronousDecayAt, mul_comm] using settles

def resonantSynchronousSettlingDuration
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) : SISecond :=
  resonantSynchronousSettlingDurationFor ((1 : ℝ) / 8)
    source input initial

theorem resonantSynchronousSettlingDuration_pos
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    0 < (resonantSynchronousSettlingDuration
      source input initial).value :=
  resonantSynchronousSettlingDurationFor_pos ((1 : ℝ) / 8)
    (by norm_num) source input initial

theorem resonantSynchronous_afterGeneratedDuration_error_lt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (physicalTime : SISecond)
    (afterGenerated :
      (resonantSynchronousSettlingDuration
        source input initial).value ≤ physicalTime.value) :
    ‖resonantActualSynchronousHilbertOutputAt
          source input initial physicalTime -
        idealQuarterOperator (encodeHilbert input)‖ < (1 : ℝ) / 8 := by
  exact resonantSynchronous_afterGeneratedDurationFor_error_lt
    ((1 : ℝ) / 8) (by norm_num) source input initial physicalTime
    afterGenerated

theorem resonantSynchronous_atGeneratedDuration_error_lt
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    ‖resonantActualSynchronousHilbertOutputAt source input initial
          (resonantSynchronousSettlingDuration source input initial) -
        idealQuarterOperator (encodeHilbert input)‖ < (1 : ℝ) / 8 :=
  resonantSynchronous_afterGeneratedDuration_error_lt
    source input initial
    (resonantSynchronousSettlingDuration source input initial) le_rfl

def resonantSynchronousSettlingDisturbance
    (source : ResonantDrivenCoreSource)
    (initial : FiniteDimensionedSeriesRLCPortState) : EndpointDisturbance :=
  fun input =>
    resonantActualSynchronousHilbertOutputAt source input initial
        (resonantSynchronousSettlingDuration source input initial) -
      idealQuarterOperator (encodeHilbert input)

theorem resonantSynchronousSettlingDisturbance_bound
    (source : ResonantDrivenCoreSource)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (input : FiniteEmbodimentState) :
    ‖resonantSynchronousSettlingDisturbance source initial input‖ <
      (1 : ℝ) / 8 :=
  resonantSynchronous_atGeneratedDuration_error_lt source input initial

theorem resonantSynchronousSettling_hasAdditiveTolerance
    (source : ResonantDrivenCoreSource)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    AdditiveDisturbanceToleranceAt idealQuarterOperator
      (resonantSynchronousSettlingDisturbance source initial) where
  linearPartTolerance := by norm_num
  disturbanceBound :=
    resonantSynchronousSettlingDisturbance_bound source initial

def resonantActualSettledSynchronousState
    (source : ResonantDrivenCoreSource)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (input : FiniteEmbodimentState) : FiniteEmbodimentState :=
  resonantActualSynchronousStateAt source input initial
    (resonantSynchronousSettlingDuration source input initial)

theorem resonantActualSettledSynchronousState_eq_disturbed
    (source : ResonantDrivenCoreSource)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (input : FiniteEmbodimentState) :
    resonantActualSettledSynchronousState source initial input =
      disturbedImplementedState idealQuarterOperator
        (resonantSynchronousSettlingDisturbance source initial) input := by
  apply complexHilbertPortEquiv.injective
  rw [complexHilbertPortEquiv_apply, complexHilbertPortEquiv_apply,
    encodeHilbert_disturbedImplementedState]
  unfold resonantActualSettledSynchronousState
    resonantSynchronousSettlingDisturbance
    resonantActualSynchronousHilbertOutputAt
  abel

end

end Producer
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.resonantSynchronousSettling_hasAdditiveTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.resonantActualSettledSynchronousState_eq_disturbed
