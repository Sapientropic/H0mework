import H0mework.Physics.Measurement.Demodulation
import H0mework.Physics.LCQuantization.Components

/-!
# Source-coded finite half-power-band interference

Every resistor/inductor sensing leg receives cosine and sine coefficients at
exactly three source-generated frequencies: the lower half-power boundary,
resonance, and the upper half-power boundary.  Thus spectral support and
amplitude are both generated from finite code; neither is a caller proof.

The code-specific L2 envelope is transported through the orthogonal
synchronous demodulator.  Its worst admissible value is proved below `1/16`,
while the actual noise at every physical time is bounded by that generated
envelope.
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
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

inductive SynchronousSenseLeg where
  | resistor
  | inductor
  deriving DecidableEq, Repr, FintypeViaProxy

inductive FiniteResonantNoiseTone where
  | lowerHalfPower
  | resonance
  | upperHalfPower
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Two quadratures for both sensing legs, all ten channels, and all three
registered band frequencies. -/
abbrev FiniteHalfPowerBandNoiseCode :=
  SynchronousSenseLeg → FiniteEmbodimentChannel →
    FiniteResonantNoiseTone →
      TernaryCalibrationOffset × TernaryCalibrationOffset

def finiteHalfPowerBandNoiseQuantum : ℝ := (1 : ℝ) / 1000

theorem finiteHalfPowerBandNoiseQuantum_pos :
    0 < finiteHalfPowerBandNoiseQuantum := by
  norm_num [finiteHalfPowerBandNoiseQuantum]

theorem ternaryNoiseCoefficient_abs_le_one
    (offset : TernaryCalibrationOffset) :
    |ternaryOffsetValue offset| ≤ 1 := by
  cases offset <;> norm_num [ternaryOffsetValue]

def finiteResonantNoiseFrequencyAt
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    FiniteResonantNoiseTone → SIHertz
  | .lowerHalfPower => lowerHalfPowerFrequencyAt
      (resonantDrivenCoreDimensionedSource source) channel
  | .resonance => sourceOwnedResonantDrivenFrequencyAt source channel
  | .upperHalfPower => upperHalfPowerFrequencyAt
      (resonantDrivenCoreDimensionedSource source) channel

theorem finiteResonantNoiseFrequency_insideHalfPowerBand
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel)
    (tone : FiniteResonantNoiseTone) :
    (lowerHalfPowerFrequencyAt
        (resonantDrivenCoreDimensionedSource source) channel).value ≤
      (finiteResonantNoiseFrequencyAt source channel tone).value ∧
    (finiteResonantNoiseFrequencyAt source channel tone).value ≤
      (upperHalfPowerFrequencyAt
        (resonantDrivenCoreDimensionedSource source) channel).value := by
  cases tone
  · exact ⟨le_rfl, (lowerHalfPower_lt_upperHalfPower
      (resonantDrivenCoreDimensionedSource source) channel).le⟩
  · have inside := (sourceGeneratedExactHalfPowerBandwidth
      (resonantDrivenCoreDimensionedSource source) channel).resonanceInside
    exact ⟨inside.1.le, inside.2.le⟩
  · exact ⟨(lowerHalfPower_lt_upperHalfPower
      (resonantDrivenCoreDimensionedSource source) channel).le, le_rfl⟩

def finiteHalfPowerBandNoiseToneAt
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel)
    (tone : FiniteResonantNoiseTone)
    (physicalTime : SISecond) : ℝ :=
  finiteHalfPowerBandNoiseQuantum *
    (ternaryOffsetValue (code leg channel tone).1 *
        Real.cos ((finiteResonantNoiseFrequencyAt
          source channel tone).value * physicalTime.value) +
      ternaryOffsetValue (code leg channel tone).2 *
        Real.sin ((finiteResonantNoiseFrequencyAt
          source channel tone).value * physicalTime.value))

def finiteHalfPowerBandNoiseAt
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : ℝ :=
  ∑ tone : FiniteResonantNoiseTone,
    finiteHalfPowerBandNoiseToneAt
      code leg source channel tone physicalTime

def finiteHalfPowerBandLegEnvelopeAt
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  finiteHalfPowerBandNoiseQuantum *
    ∑ tone : FiniteResonantNoiseTone,
      (|ternaryOffsetValue (code leg channel tone).1| +
        |ternaryOffsetValue (code leg channel tone).2|)

theorem finiteHalfPowerBandLegEnvelope_nonneg
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ finiteHalfPowerBandLegEnvelopeAt code leg channel := by
  unfold finiteHalfPowerBandLegEnvelopeAt
  exact mul_nonneg finiteHalfPowerBandNoiseQuantum_pos.le
    (Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem finiteHalfPowerBandNoiseTone_abs_le
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel)
    (tone : FiniteResonantNoiseTone)
    (physicalTime : SISecond) :
    |finiteHalfPowerBandNoiseToneAt
      code leg source channel tone physicalTime| ≤
      finiteHalfPowerBandNoiseQuantum *
        (|ternaryOffsetValue (code leg channel tone).1| +
          |ternaryOffsetValue (code leg channel tone).2|) := by
  unfold finiteHalfPowerBandNoiseToneAt
  rw [abs_mul, abs_of_pos finiteHalfPowerBandNoiseQuantum_pos]
  apply mul_le_mul_of_nonneg_left _ finiteHalfPowerBandNoiseQuantum_pos.le
  calc
    |ternaryOffsetValue (code leg channel tone).1 *
          Real.cos ((finiteResonantNoiseFrequencyAt
            source channel tone).value * physicalTime.value) +
        ternaryOffsetValue (code leg channel tone).2 *
          Real.sin ((finiteResonantNoiseFrequencyAt
            source channel tone).value * physicalTime.value)| ≤
      |ternaryOffsetValue (code leg channel tone).1 *
          Real.cos ((finiteResonantNoiseFrequencyAt
            source channel tone).value * physicalTime.value)| +
        |ternaryOffsetValue (code leg channel tone).2 *
          Real.sin ((finiteResonantNoiseFrequencyAt
            source channel tone).value * physicalTime.value)| := abs_add_le _ _
    _ ≤ |ternaryOffsetValue (code leg channel tone).1| * 1 +
        |ternaryOffsetValue (code leg channel tone).2| * 1 := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
          (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
          (abs_nonneg _))
    _ = _ := by ring

theorem finiteHalfPowerBandNoise_abs_le_envelope
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    |finiteHalfPowerBandNoiseAt code leg source channel physicalTime| ≤
      finiteHalfPowerBandLegEnvelopeAt code leg channel := by
  unfold finiteHalfPowerBandNoiseAt finiteHalfPowerBandLegEnvelopeAt
  calc
    |∑ tone : FiniteResonantNoiseTone,
        finiteHalfPowerBandNoiseToneAt
          code leg source channel tone physicalTime| ≤
      ∑ tone : FiniteResonantNoiseTone,
        |finiteHalfPowerBandNoiseToneAt
          code leg source channel tone physicalTime| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ tone : FiniteResonantNoiseTone,
        finiteHalfPowerBandNoiseQuantum *
          (|ternaryOffsetValue (code leg channel tone).1| +
            |ternaryOffsetValue (code leg channel tone).2|) := by
      exact Finset.sum_le_sum fun tone _ =>
        finiteHalfPowerBandNoiseTone_abs_le
          code leg source channel tone physicalTime
    _ = finiteHalfPowerBandNoiseQuantum *
        ∑ tone : FiniteResonantNoiseTone,
          (|ternaryOffsetValue (code leg channel tone).1| +
            |ternaryOffsetValue (code leg channel tone).2|) := by
      rw [Finset.mul_sum]

theorem finiteHalfPowerBandLegEnvelope_le_sixQuantum
    (code : FiniteHalfPowerBandNoiseCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteHalfPowerBandLegEnvelopeAt code leg channel ≤
      6 * finiteHalfPowerBandNoiseQuantum := by
  unfold finiteHalfPowerBandLegEnvelopeAt
  have sumLe :
    ∑ tone : FiniteResonantNoiseTone,
        (|ternaryOffsetValue (code leg channel tone).1| +
          |ternaryOffsetValue (code leg channel tone).2|) ≤
      6 := by
    calc
      _ ≤ ∑ _tone : FiniteResonantNoiseTone, (2 : ℝ) := by
        exact Finset.sum_le_sum fun tone _ => by
          have first := ternaryNoiseCoefficient_abs_le_one
            (code leg channel tone).1
          have second := ternaryNoiseCoefficient_abs_le_one
            (code leg channel tone).2
          linarith
      _ = 6 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num [show Fintype.card FiniteResonantNoiseTone = 3 by decide]
  calc
    finiteHalfPowerBandNoiseQuantum *
        ∑ tone : FiniteResonantNoiseTone,
          (|ternaryOffsetValue (code leg channel tone).1| +
            |ternaryOffsetValue (code leg channel tone).2|) ≤
      finiteHalfPowerBandNoiseQuantum * 6 :=
        mul_le_mul_of_nonneg_left sumLe
          finiteHalfPowerBandNoiseQuantum_pos.le
    _ = 6 * finiteHalfPowerBandNoiseQuantum := by ring

def finiteHalfPowerBandNoiseEnvelopeSq
    (code : FiniteHalfPowerBandNoiseCode) : ℝ :=
  ∑ channel : FiniteEmbodimentChannel,
    (finiteHalfPowerBandLegEnvelopeAt code .resistor channel ^ 2 +
      finiteHalfPowerBandLegEnvelopeAt code .inductor channel ^ 2)

def finiteHalfPowerBandNoiseBudget
    (code : FiniteHalfPowerBandNoiseCode) : ℝ :=
  Real.sqrt (finiteHalfPowerBandNoiseEnvelopeSq code)

theorem finiteHalfPowerBandNoiseEnvelopeSq_nonneg
    (code : FiniteHalfPowerBandNoiseCode) :
    0 ≤ finiteHalfPowerBandNoiseEnvelopeSq code := by
  unfold finiteHalfPowerBandNoiseEnvelopeSq
  exact Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem finiteHalfPowerBandNoiseBudget_nonneg
    (code : FiniteHalfPowerBandNoiseCode) :
    0 ≤ finiteHalfPowerBandNoiseBudget code :=
  Real.sqrt_nonneg _

theorem finiteHalfPowerBandNoiseEnvelopeSq_le
    (code : FiniteHalfPowerBandNoiseCode) :
    finiteHalfPowerBandNoiseEnvelopeSq code ≤
      720 * finiteHalfPowerBandNoiseQuantum ^ 2 := by
  unfold finiteHalfPowerBandNoiseEnvelopeSq
  calc
    ∑ channel : FiniteEmbodimentChannel,
        (finiteHalfPowerBandLegEnvelopeAt code .resistor channel ^ 2 +
          finiteHalfPowerBandLegEnvelopeAt code .inductor channel ^ 2) ≤
      ∑ _channel : FiniteEmbodimentChannel,
        (72 * finiteHalfPowerBandNoiseQuantum ^ 2) := by
      exact Finset.sum_le_sum fun channel _ => by
        have resistor := finiteHalfPowerBandLegEnvelope_le_sixQuantum
          code .resistor channel
        have inductor := finiteHalfPowerBandLegEnvelope_le_sixQuantum
          code .inductor channel
        have rightNonneg : 0 ≤ 6 * finiteHalfPowerBandNoiseQuantum :=
          mul_nonneg (by norm_num) finiteHalfPowerBandNoiseQuantum_pos.le
        have resistorSq :
            finiteHalfPowerBandLegEnvelopeAt
                code .resistor channel ^ 2 ≤
              (6 * finiteHalfPowerBandNoiseQuantum) ^ 2 := (sq_le_sq).2 (by
          rw [abs_of_nonneg rightNonneg,
            abs_of_nonneg (finiteHalfPowerBandLegEnvelope_nonneg
              code .resistor channel)]
          exact resistor)
        have inductorSq :
            finiteHalfPowerBandLegEnvelopeAt
                code .inductor channel ^ 2 ≤
              (6 * finiteHalfPowerBandNoiseQuantum) ^ 2 := (sq_le_sq).2 (by
          rw [abs_of_nonneg rightNonneg,
            abs_of_nonneg (finiteHalfPowerBandLegEnvelope_nonneg
              code .inductor channel)]
          exact inductor)
        calc
          _ ≤ (6 * finiteHalfPowerBandNoiseQuantum) ^ 2 +
              (6 * finiteHalfPowerBandNoiseQuantum) ^ 2 :=
            add_le_add resistorSq inductorSq
          _ = _ := by ring
    _ = 720 * finiteHalfPowerBandNoiseQuantum ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_num [show Fintype.card FiniteEmbodimentChannel = 10 from
        channel_cardinality]
      ring

theorem finiteHalfPowerBandNoiseBudget_lt_sixteenth
    (code : FiniteHalfPowerBandNoiseCode) :
    finiteHalfPowerBandNoiseBudget code < (1 : ℝ) / 16 := by
  have envelopeBound := finiteHalfPowerBandNoiseEnvelopeSq_le code
  have budgetSquare := Real.sq_sqrt
    (finiteHalfPowerBandNoiseEnvelopeSq_nonneg code)
  have numeric :
      720 * finiteHalfPowerBandNoiseQuantum ^ 2 <
        ((1 : ℝ) / 16) ^ 2 := by
    norm_num [finiteHalfPowerBandNoiseQuantum]
  unfold finiteHalfPowerBandNoiseBudget
  nlinarith [Real.sqrt_nonneg (finiteHalfPowerBandNoiseEnvelopeSq code)]

def finiteHalfPowerBandSynchronousNoiseStateAt
    (code : FiniteHalfPowerBandNoiseCode)
    (source : ResonantDrivenCoreSource)
    (physicalTime : SISecond) : FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source channel physicalTime)
    (finiteHalfPowerBandNoiseAt code .resistor source channel physicalTime)
    (finiteHalfPowerBandNoiseAt code .inductor source channel physicalTime)

def finiteHalfPowerBandSynchronousHilbertNoiseAt
    (code : FiniteHalfPowerBandNoiseCode)
    (source : ResonantDrivenCoreSource)
    (physicalTime : SISecond) : HilbertEmbodimentState :=
  encodeHilbert
    (finiteHalfPowerBandSynchronousNoiseStateAt code source physicalTime)

theorem finiteHalfPowerBandSynchronousNoise_channelEnergy_eq
    (code : FiniteHalfPowerBandNoiseCode)
    (source : ResonantDrivenCoreSource)
    (physicalTime : SISecond)
    (channel : FiniteEmbodimentChannel) :
    channelEnergy
        (finiteHalfPowerBandSynchronousNoiseStateAt
          code source physicalTime) channel =
      finiteHalfPowerBandNoiseAt
          code .resistor source channel physicalTime ^ 2 +
        finiteHalfPowerBandNoiseAt
          code .inductor source channel physicalTime ^ 2 := by
  unfold channelEnergy sourcePort targetPort
    finiteHalfPowerBandSynchronousNoiseStateAt
    synchronousDemodulatedPortAt
  have circle := Real.sin_sq_add_cos_sq
    (resonantSynchronousPhaseAt source channel physicalTime)
  calc
    _ = (Real.sin
            (resonantSynchronousPhaseAt source channel physicalTime) ^ 2 +
          Real.cos
            (resonantSynchronousPhaseAt source channel physicalTime) ^ 2) *
        (finiteHalfPowerBandNoiseAt
            code .resistor source channel physicalTime ^ 2 +
          finiteHalfPowerBandNoiseAt
            code .inductor source channel physicalTime ^ 2) := by ring
    _ = _ := by rw [circle]; ring

theorem finiteHalfPowerBandSynchronousNoise_energy_le_envelope
    (code : FiniteHalfPowerBandNoiseCode)
    (source : ResonantDrivenCoreSource)
    (physicalTime : SISecond) :
    energy (finiteHalfPowerBandSynchronousNoiseStateAt
      code source physicalTime) ≤
      finiteHalfPowerBandNoiseEnvelopeSq code := by
  unfold energy finiteHalfPowerBandNoiseEnvelopeSq
  exact Finset.sum_le_sum fun channel _ => by
    rw [finiteHalfPowerBandSynchronousNoise_channelEnergy_eq]
    have resistor := finiteHalfPowerBandNoise_abs_le_envelope
      code .resistor source channel physicalTime
    have inductor := finiteHalfPowerBandNoise_abs_le_envelope
      code .inductor source channel physicalTime
    exact add_le_add ((sq_le_sq).2 (by
      rw [abs_of_nonneg (finiteHalfPowerBandLegEnvelope_nonneg
        code .resistor channel)]
      exact resistor)) ((sq_le_sq).2 (by
      rw [abs_of_nonneg (finiteHalfPowerBandLegEnvelope_nonneg
        code .inductor channel)]
      exact inductor))

theorem finiteHalfPowerBandSynchronousHilbertNoise_norm_le_budget
    (code : FiniteHalfPowerBandNoiseCode)
    (source : ResonantDrivenCoreSource)
    (physicalTime : SISecond) :
    ‖finiteHalfPowerBandSynchronousHilbertNoiseAt
      code source physicalTime‖ ≤ finiteHalfPowerBandNoiseBudget code := by
  have energyBound := finiteHalfPowerBandSynchronousNoise_energy_le_envelope
    code source physicalTime
  rw [energy_eq_encodeHilbert_norm_sq] at energyBound
  have budgetSquare := Real.sq_sqrt
    (finiteHalfPowerBandNoiseEnvelopeSq_nonneg code)
  unfold finiteHalfPowerBandSynchronousHilbertNoiseAt
    finiteHalfPowerBandNoiseBudget
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [budgetSquare]
  exact energyBound

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteHalfPowerBandNoiseBudget_lt_sixteenth
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteHalfPowerBandSynchronousHilbertNoise_norm_le_budget
