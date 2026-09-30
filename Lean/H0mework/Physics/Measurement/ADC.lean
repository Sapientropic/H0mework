import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Order
import H0mework.Physics.Measurement.Voltage

/-!
# Finite ADC and source-generated discrete sampling clock

Three finite ADC resolutions quantize dimensionless voltage ratios downward.
The affine meter's zero/span values lie exactly on every generated grid, while
an arbitrary operational voltage has a strict one-step error bound.

Three finite clock divisors generate positive SI tick periods from the RLC
time scale.  The sampling compiler uses the ceiling tick, so the actual sample
time is never earlier than the requested settling duration and overshoots it
by less than one generated tick.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

inductive FiniteADCResolutionCode where
  | coarse
  | medium
  | fine
  deriving DecidableEq, Repr, FintypeViaProxy

def finiteADCNormalizedStep : FiniteADCResolutionCode → ℝ
  | .coarse => (1 : ℝ) / 250000
  | .medium => (1 : ℝ) / 500000
  | .fine => (1 : ℝ) / 1000000

def finiteADCGridDenominator : FiniteADCResolutionCode → ℤ
  | .coarse => 250000
  | .medium => 500000
  | .fine => 1000000

theorem finiteADCGridDenominator_pos
    (code : FiniteADCResolutionCode) :
    0 < finiteADCGridDenominator code := by
  cases code <;> norm_num [finiteADCGridDenominator]

theorem finiteADCNormalizedStep_eq_invDenominator
    (code : FiniteADCResolutionCode) :
    finiteADCNormalizedStep code =
      ((finiteADCGridDenominator code : ℤ) : ℝ)⁻¹ := by
  cases code <;>
    norm_num [finiteADCNormalizedStep, finiteADCGridDenominator]

/-- Literal finite ADC alphabet.  The signed code is bounded to the normalized
full-scale interval `[-16, 16]`; unlike the floor helper below, this carrier is
genuinely finite. -/
abbrev FiniteADCWord (code : FiniteADCResolutionCode) :=
  Set.Icc (-(16 * finiteADCGridDenominator code))
    (16 * finiteADCGridDenominator code)

def finiteADCClampIndex
    (code : FiniteADCResolutionCode) (signal : ℝ) : ℤ :=
  max (-(16 * finiteADCGridDenominator code))
    (min ⌊signal / finiteADCNormalizedStep code⌋
      (16 * finiteADCGridDenominator code))

def finiteADCEncodeNormalized
    (code : FiniteADCResolutionCode) (signal : ℝ) : FiniteADCWord code := by
  refine ⟨finiteADCClampIndex code signal, ?_, ?_⟩
  · exact le_max_left _ _
  · apply max_le
    · have positive := finiteADCGridDenominator_pos code
      omega
    · exact min_le_right _ _

def finiteADCDecodeNormalized
    (code : FiniteADCResolutionCode) (word : FiniteADCWord code) : ℝ :=
  finiteADCNormalizedStep code * (word.val : ℝ)

theorem finiteADCClampIndex_eq_floor_of_inRange
    (code : FiniteADCResolutionCode) (signal : ℝ)
    (lower : (-16 : ℝ) ≤ signal) (upper : signal < 16) :
    finiteADCClampIndex code signal =
      ⌊signal / finiteADCNormalizedStep code⌋ := by
  have lowerFloor :
      -(16 * finiteADCGridDenominator code) ≤
        ⌊signal / finiteADCNormalizedStep code⌋ := by
    rw [Int.le_floor]
    cases code <;>
      norm_num [finiteADCNormalizedStep, finiteADCGridDenominator] at * <;>
      linarith
  have upperFloor :
      ⌊signal / finiteADCNormalizedStep code⌋ ≤
        16 * finiteADCGridDenominator code := by
    have strict :
        ⌊signal / finiteADCNormalizedStep code⌋ <
          16 * finiteADCGridDenominator code + 1 := by
      rw [Int.floor_lt]
      cases code <;>
        norm_num [finiteADCNormalizedStep, finiteADCGridDenominator] at * <;>
        linarith
    omega
  simp [finiteADCClampIndex, lowerFloor, upperFloor]

theorem finiteADCNormalizedStep_pos
    (code : FiniteADCResolutionCode) :
    0 < finiteADCNormalizedStep code := by
  cases code <;> norm_num [finiteADCNormalizedStep]

theorem finiteADCNormalizedStep_le_coarse
    (code : FiniteADCResolutionCode) :
    finiteADCNormalizedStep code ≤ (1 : ℝ) / 250000 := by
  cases code <;> norm_num [finiteADCNormalizedStep]

def finiteADCQuantizeNormalizedDown
    (code : FiniteADCResolutionCode) (signal : ℝ) : ℝ :=
  finiteADCNormalizedStep code *
    (⌊signal / finiteADCNormalizedStep code⌋ : ℝ)

theorem finiteADCQuantizeNormalizedDown_error
    (code : FiniteADCResolutionCode) (signal : ℝ) :
    0 ≤ signal - finiteADCQuantizeNormalizedDown code signal ∧
      signal - finiteADCQuantizeNormalizedDown code signal <
        finiteADCNormalizedStep code := by
  have stepPositive := finiteADCNormalizedStep_pos code
  have lower := Int.floor_le (signal / finiteADCNormalizedStep code)
  have upper := Int.lt_floor_add_one
    (signal / finiteADCNormalizedStep code)
  have lowerScaled := mul_le_mul_of_nonneg_left lower stepPositive.le
  have upperScaled := mul_lt_mul_of_pos_left upper stepPositive
  constructor
  · unfold finiteADCQuantizeNormalizedDown
    have quantizedLe :
        finiteADCNormalizedStep code *
            (⌊signal / finiteADCNormalizedStep code⌋ : ℝ) ≤ signal := by
      calc
        _ ≤ finiteADCNormalizedStep code *
            (signal / finiteADCNormalizedStep code) := lowerScaled
        _ = signal := by field_simp [ne_of_gt stepPositive]
    linarith
  · unfold finiteADCQuantizeNormalizedDown
    have signalLt : signal < finiteADCNormalizedStep code *
        ((⌊signal / finiteADCNormalizedStep code⌋ : ℝ) + 1) := by
      calc
        signal = finiteADCNormalizedStep code *
            (signal / finiteADCNormalizedStep code) := by
              field_simp [ne_of_gt stepPositive]
        _ < _ := upperScaled
    linarith

theorem finiteADCDecode_encode_eq_gridQuantization_of_inRange
    (code : FiniteADCResolutionCode) (signal : ℝ)
    (lower : (-16 : ℝ) ≤ signal) (upper : signal < 16) :
    finiteADCDecodeNormalized code
        (finiteADCEncodeNormalized code signal) =
      finiteADCQuantizeNormalizedDown code signal := by
  simp [finiteADCDecodeNormalized, finiteADCEncodeNormalized,
    finiteADCQuantizeNormalizedDown,
    finiteADCClampIndex_eq_floor_of_inRange code signal lower upper]

theorem finiteADCDecode_encode_error_of_inRange
    (code : FiniteADCResolutionCode) (signal : ℝ)
    (lower : (-16 : ℝ) ≤ signal) (upper : signal < 16) :
    0 ≤ signal - finiteADCDecodeNormalized code
        (finiteADCEncodeNormalized code signal) ∧
      signal - finiteADCDecodeNormalized code
          (finiteADCEncodeNormalized code signal) <
        finiteADCNormalizedStep code := by
  rw [finiteADCDecode_encode_eq_gridQuantization_of_inRange
    code signal lower upper]
  exact finiteADCQuantizeNormalizedDown_error code signal

def finiteADCQuantizeVoltage
    (code : FiniteADCResolutionCode)
    (scale voltage : SIVolt) : SIVolt :=
  finiteADCQuantizeNormalizedDown code (voltage.value / scale.value) • scale

def finiteADCEncodeVoltage
    (code : FiniteADCResolutionCode)
    (scale voltage : SIVolt) : FiniteADCWord code :=
  finiteADCEncodeNormalized code (voltage.value / scale.value)

def finiteADCDecodeVoltage
    (code : FiniteADCResolutionCode)
    (scale : SIVolt) (word : FiniteADCWord code) : SIVolt :=
  finiteADCDecodeNormalized code word • scale

theorem finiteADCDecodeEncodeVoltage_normalizedError_lt
    (code : FiniteADCResolutionCode)
    (scale voltage : SIVolt) (scalePositive : 0 < scale.value)
    (lower : (-16 : ℝ) ≤ voltage.value / scale.value)
    (upper : voltage.value / scale.value < 16) :
    |(finiteADCDecodeVoltage code scale
          (finiteADCEncodeVoltage code scale voltage)).value /
          scale.value - voltage.value / scale.value| <
      finiteADCNormalizedStep code := by
  have error := finiteADCDecode_encode_error_of_inRange code
    (voltage.value / scale.value) lower upper
  unfold finiteADCDecodeVoltage finiteADCEncodeVoltage
  simp only [SIQuantity.smul_value]
  rw [mul_div_cancel_right₀ _ (ne_of_gt scalePositive)]
  rw [abs_sub_comm, abs_of_nonneg error.1]
  exact error.2

theorem finiteADCQuantizeVoltage_normalizedError_lt
    (code : FiniteADCResolutionCode)
    (scale voltage : SIVolt) (scalePositive : 0 < scale.value) :
    |(finiteADCQuantizeVoltage code scale voltage).value / scale.value -
        voltage.value / scale.value| < finiteADCNormalizedStep code := by
  have error := finiteADCQuantizeNormalizedDown_error code
    (voltage.value / scale.value)
  unfold finiteADCQuantizeVoltage
  simp only [SIQuantity.smul_value]
  rw [mul_div_cancel_right₀ _ (ne_of_gt scalePositive)]
  rw [abs_sub_comm, abs_of_nonneg error.1]
  exact error.2

theorem finiteADCQuantizeNormalizedDown_ternaryThousandth_exact
    (adcCode : FiniteADCResolutionCode)
    (offsetCode : TernaryCalibrationOffset) :
    finiteADCQuantizeNormalizedDown adcCode
        (ternaryOffsetValue offsetCode / 1000) =
      ternaryOffsetValue offsetCode / 1000 := by
  cases adcCode <;> cases offsetCode <;>
    norm_num [finiteADCQuantizeNormalizedDown,
      finiteADCNormalizedStep, ternaryOffsetValue]

theorem finiteADCQuantizeNormalizedDown_affineSpan_exact
    (adcCode : FiniteADCResolutionCode)
    (gainCode offsetCode : TernaryCalibrationOffset) :
    finiteADCQuantizeNormalizedDown adcCode
        (1 + ternaryOffsetValue gainCode / 1000 +
          ternaryOffsetValue offsetCode / 1000) =
      1 + ternaryOffsetValue gainCode / 1000 +
        ternaryOffsetValue offsetCode / 1000 := by
  cases adcCode <;> cases gainCode <;> cases offsetCode <;>
    norm_num [finiteADCQuantizeNormalizedDown,
      finiteADCNormalizedStep, ternaryOffsetValue]

theorem finiteADCQuantizeVoltage_exact_of_normalized
    (adcCode : FiniteADCResolutionCode)
    (scale voltage : SIVolt)
    (scaleNonzero : scale.value ≠ 0)
    (exact : finiteADCQuantizeNormalizedDown adcCode
        (voltage.value / scale.value) = voltage.value / scale.value) :
    finiteADCQuantizeVoltage adcCode scale voltage = voltage := by
  apply SIQuantity.ext
  simp only [finiteADCQuantizeVoltage, SIQuantity.smul_value]
  rw [exact]
  exact div_mul_cancel₀ voltage.value scaleNonzero

theorem finiteADCDecodeEncodeVoltage_exact_of_normalized
    (adcCode : FiniteADCResolutionCode)
    (scale voltage : SIVolt)
    (scaleNonzero : scale.value ≠ 0)
    (lower : (-16 : ℝ) ≤ voltage.value / scale.value)
    (upper : voltage.value / scale.value < 16)
    (exact : finiteADCQuantizeNormalizedDown adcCode
        (voltage.value / scale.value) = voltage.value / scale.value) :
    finiteADCDecodeVoltage adcCode scale
        (finiteADCEncodeVoltage adcCode scale voltage) = voltage := by
  apply SIQuantity.ext
  simp only [finiteADCDecodeVoltage, finiteADCEncodeVoltage,
    SIQuantity.smul_value]
  rw [finiteADCDecode_encode_eq_gridQuantization_of_inRange
    adcCode _ lower upper, exact]
  exact div_mul_cancel₀ voltage.value scaleNonzero

theorem finiteADCQuantizeMeterZeroReference_exact
    (adcCode : FiniteADCResolutionCode)
    (meterCode : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCQuantizeVoltage adcCode
        (finiteAffineMeterSenseScaleAt source leg channel)
        (finiteAffineMeterZeroReferenceAt meterCode source leg channel) =
      finiteAffineMeterZeroReferenceAt meterCode source leg channel := by
  have scaleNonzero := ne_of_gt
    (finiteAffineMeterSenseScale_pos source leg channel)
  apply finiteADCQuantizeVoltage_exact_of_normalized
    adcCode _ _ scaleNonzero
  have normalized :
      (finiteAffineMeterZeroReferenceAt meterCode source leg channel).value /
          (finiteAffineMeterSenseScaleAt source leg channel).value =
        ternaryOffsetValue (meterCode leg channel).2 / 1000 := by
    unfold finiteAffineMeterZeroReferenceAt finiteAffineMeterRawAt
      finiteAffineMeterOffsetAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value,
      SIQuantity.zero_value, mul_zero, zero_add]
    field_simp [scaleNonzero]
  rw [normalized]
  exact finiteADCQuantizeNormalizedDown_ternaryThousandth_exact
    adcCode (meterCode leg channel).2

theorem finiteADCQuantizeMeterSpanReference_exact
    (adcCode : FiniteADCResolutionCode)
    (meterCode : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCQuantizeVoltage adcCode
        (finiteAffineMeterSenseScaleAt source leg channel)
        (finiteAffineMeterSpanReferenceAt meterCode source leg channel) =
      finiteAffineMeterSpanReferenceAt meterCode source leg channel := by
  have scaleNonzero := ne_of_gt
    (finiteAffineMeterSenseScale_pos source leg channel)
  apply finiteADCQuantizeVoltage_exact_of_normalized
    adcCode _ _ scaleNonzero
  have normalized :
      (finiteAffineMeterSpanReferenceAt meterCode source leg channel).value /
          (finiteAffineMeterSenseScaleAt source leg channel).value =
        1 + ternaryOffsetValue (meterCode leg channel).1 / 1000 +
          ternaryOffsetValue (meterCode leg channel).2 / 1000 := by
    unfold finiteAffineMeterSpanReferenceAt finiteAffineMeterRawAt
      finiteAffineMeterOffsetAt finiteAffineMeterGainAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value]
    field_simp [scaleNonzero]
  rw [normalized]
  exact finiteADCQuantizeNormalizedDown_affineSpan_exact
    adcCode (meterCode leg channel).1 (meterCode leg channel).2

theorem finiteADCDecodeEncodeMeterZeroReference_exact
    (adcCode : FiniteADCResolutionCode)
    (meterCode : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCDecodeVoltage adcCode
        (finiteAffineMeterSenseScaleAt source leg channel)
        (finiteADCEncodeVoltage adcCode
          (finiteAffineMeterSenseScaleAt source leg channel)
          (finiteAffineMeterZeroReferenceAt meterCode source leg channel)) =
      finiteAffineMeterZeroReferenceAt meterCode source leg channel := by
  have scaleNonzero := ne_of_gt
    (finiteAffineMeterSenseScale_pos source leg channel)
  have normalized :
      (finiteAffineMeterZeroReferenceAt meterCode source leg channel).value /
          (finiteAffineMeterSenseScaleAt source leg channel).value =
        ternaryOffsetValue (meterCode leg channel).2 / 1000 := by
    unfold finiteAffineMeterZeroReferenceAt finiteAffineMeterRawAt
      finiteAffineMeterOffsetAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value,
      SIQuantity.zero_value, mul_zero, zero_add]
    field_simp [scaleNonzero]
  apply finiteADCDecodeEncodeVoltage_exact_of_normalized
    adcCode _ _ scaleNonzero
  · rw [normalized]
    cases (meterCode leg channel).2 <;> norm_num [ternaryOffsetValue]
  · rw [normalized]
    cases (meterCode leg channel).2 <;> norm_num [ternaryOffsetValue]
  · rw [normalized]
    exact finiteADCQuantizeNormalizedDown_ternaryThousandth_exact
      adcCode (meterCode leg channel).2

theorem finiteADCDecodeEncodeMeterSpanReference_exact
    (adcCode : FiniteADCResolutionCode)
    (meterCode : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCDecodeVoltage adcCode
        (finiteAffineMeterSenseScaleAt source leg channel)
        (finiteADCEncodeVoltage adcCode
          (finiteAffineMeterSenseScaleAt source leg channel)
          (finiteAffineMeterSpanReferenceAt meterCode source leg channel)) =
      finiteAffineMeterSpanReferenceAt meterCode source leg channel := by
  have scaleNonzero := ne_of_gt
    (finiteAffineMeterSenseScale_pos source leg channel)
  have normalized :
      (finiteAffineMeterSpanReferenceAt meterCode source leg channel).value /
          (finiteAffineMeterSenseScaleAt source leg channel).value =
        1 + ternaryOffsetValue (meterCode leg channel).1 / 1000 +
          ternaryOffsetValue (meterCode leg channel).2 / 1000 := by
    unfold finiteAffineMeterSpanReferenceAt finiteAffineMeterRawAt
      finiteAffineMeterOffsetAt finiteAffineMeterGainAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value]
    field_simp [scaleNonzero]
  apply finiteADCDecodeEncodeVoltage_exact_of_normalized
    adcCode _ _ scaleNonzero
  · rw [normalized]
    cases (meterCode leg channel).1 <;>
      cases (meterCode leg channel).2 <;> norm_num [ternaryOffsetValue]
  · rw [normalized]
    cases (meterCode leg channel).1 <;>
      cases (meterCode leg channel).2 <;> norm_num [ternaryOffsetValue]
  · rw [normalized]
    exact finiteADCQuantizeNormalizedDown_affineSpan_exact adcCode
      (meterCode leg channel).1 (meterCode leg channel).2

inductive FiniteSamplingClockCode where
  | coarse
  | medium
  | fine
  deriving DecidableEq, Repr, FintypeViaProxy

def finiteSamplingClockDivisor : FiniteSamplingClockCode → ℝ
  | .coarse => 1000
  | .medium => 2000
  | .fine => 4000

theorem finiteSamplingClockDivisor_pos
    (code : FiniteSamplingClockCode) :
    0 < finiteSamplingClockDivisor code := by
  cases code <;> norm_num [finiteSamplingClockDivisor]

def finiteSamplingClockTickPeriod
    (source : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) : SISecond :=
  (finiteSamplingClockDivisor code)⁻¹ • source.2.timeScale

theorem finiteSamplingClockTickPeriod_pos
    (source : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) :
    0 < (finiteSamplingClockTickPeriod source code).value := by
  simp only [finiteSamplingClockTickPeriod, SIQuantity.smul_value]
  exact mul_pos (inv_pos.mpr (finiteSamplingClockDivisor_pos code))
    source.2.timeScalePositive

def finiteSamplingClockTickCount
    (source : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode)
    (requested : SISecond) : ℕ :=
  Nat.ceil (requested.value /
    (finiteSamplingClockTickPeriod source code).value)

def finiteSamplingClockSampleTime
    (source : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode)
    (requested : SISecond) : SISecond :=
  (finiteSamplingClockTickCount source code requested : ℝ) •
    finiteSamplingClockTickPeriod source code

theorem finiteSamplingClock_requested_le_sampleTime
    (source : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode)
    (requested : SISecond) :
    requested.value ≤
      (finiteSamplingClockSampleTime source code requested).value := by
  have tickPositive := finiteSamplingClockTickPeriod_pos source code
  have ceiling := Nat.le_ceil
    (requested.value /
      (finiteSamplingClockTickPeriod source code).value)
  have scaled := mul_le_mul_of_nonneg_right ceiling tickPositive.le
  simp only [finiteSamplingClockSampleTime,
    finiteSamplingClockTickCount, SIQuantity.smul_value]
  calc
    requested.value =
        (requested.value /
          (finiteSamplingClockTickPeriod source code).value) *
          (finiteSamplingClockTickPeriod source code).value := by
            field_simp [ne_of_gt tickPositive]
    _ ≤ _ := scaled

theorem finiteSamplingClock_sampleTime_lt_requested_add_tick
    (source : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode)
    (requested : SISecond) (requestedNonnegative : 0 ≤ requested.value) :
    (finiteSamplingClockSampleTime source code requested).value <
      requested.value + (finiteSamplingClockTickPeriod source code).value := by
  have tickPositive := finiteSamplingClockTickPeriod_pos source code
  have ratioNonnegative :
      0 ≤ requested.value /
        (finiteSamplingClockTickPeriod source code).value :=
    div_nonneg requestedNonnegative tickPositive.le
  have ceiling := Nat.ceil_lt_add_one ratioNonnegative
  have scaled := mul_lt_mul_of_pos_right ceiling tickPositive
  simp only [finiteSamplingClockSampleTime,
    finiteSamplingClockTickCount, SIQuantity.smul_value]
  calc
    (Nat.ceil
        (requested.value /
          (finiteSamplingClockTickPeriod source code).value) : ℝ) *
        (finiteSamplingClockTickPeriod source code).value <
      (requested.value /
          (finiteSamplingClockTickPeriod source code).value + 1) *
        (finiteSamplingClockTickPeriod source code).value := scaled
    _ = requested.value +
        (finiteSamplingClockTickPeriod source code).value := by
      field_simp [ne_of_gt tickPositive]

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCQuantizeNormalizedDown_error
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCDecode_encode_error_of_inRange
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCDecodeEncodeMeterSpanReference_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteSamplingClock_requested_le_sampleTime
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteSamplingClock_sampleTime_lt_requested_add_tick
