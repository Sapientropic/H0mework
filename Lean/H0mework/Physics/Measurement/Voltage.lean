import H0mework.Physics.Measurement.Noise

/-!
# Source-generated two-point affine voltage metrology

Each sensing leg/channel has a finite gain/offset code.  The compiler emits
zero-reference, span-reference, and operational raw voltages through the same
affine meter.  The decoder sees only those raw rows and the source-generated
physical span scale; it does not read the hidden code.

The zero/span rows recover gain and offset exactly, so calibrated operational
readback equals the underlying physical voltage divided by the correct leg
scale.  Calibration correctness is a compiler theorem, not an input field.
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
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

inductive FiniteAffineMeterFrame where
  | zeroReference
  | spanReference
  | operational
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Gain code and physical offset code for every leg/channel. -/
abbrev FiniteAffineMeterCode :=
  SynchronousSenseLeg → FiniteEmbodimentChannel →
    TernaryCalibrationOffset × TernaryCalibrationOffset

def finiteAffineMeterGainAt
    (code : FiniteAffineMeterCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  1 + ternaryOffsetValue (code leg channel).1 / 1000

theorem finiteAffineMeterGain_pos
    (code : FiniteAffineMeterCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    0 < finiteAffineMeterGainAt code leg channel := by
  cases gainCode : (code leg channel).1 <;>
    norm_num [finiteAffineMeterGainAt, ternaryOffsetValue, gainCode]

def finiteAffineMeterSenseScaleAt
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  match leg with
  | .resistor => source.2.voltageScale
  | .inductor => resonantInductorOutputScaleAt
      (resonantDrivenCoreDimensionedSource source) channel

theorem finiteAffineMeterSenseScale_pos
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    0 < (finiteAffineMeterSenseScaleAt source leg channel).value := by
  cases leg
  · exact source.2.voltageScalePositive
  · exact resonantInductorOutputScale_pos
      (resonantDrivenCoreDimensionedSource source) channel

def finiteAffineMeterOffsetAt
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  (ternaryOffsetValue (code leg channel).2 / 1000) •
    finiteAffineMeterSenseScaleAt source leg channel

def finiteAffineMeterRawAt
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalVoltage : SIVolt) : SIVolt :=
  finiteAffineMeterGainAt code leg channel • physicalVoltage +
    finiteAffineMeterOffsetAt code source leg channel

def finiteAffineMeterZeroReferenceAt
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  finiteAffineMeterRawAt code source leg channel 0

def finiteAffineMeterSpanReferenceAt
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  finiteAffineMeterRawAt code source leg channel
    (finiteAffineMeterSenseScaleAt source leg channel)

/-- Decoder-visible gain from two raw reference frames. -/
def decodedFiniteAffineMeterGain
    (zeroReference spanReference spanScale : SIVolt) : ℝ :=
  (spanReference - zeroReference).value / spanScale.value

/-- Decoder-visible normalized read.  Only raw reference/operational rows and
the public span scale are arguments. -/
def decodedFiniteAffineMeterNormalizedRead
    (zeroReference spanReference operational spanScale : SIVolt) : ℝ :=
  ((operational - zeroReference).value / spanScale.value) /
    decodedFiniteAffineMeterGain zeroReference spanReference spanScale

theorem finiteAffineMeterZeroReference_eq_offset
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteAffineMeterZeroReferenceAt code source leg channel =
      finiteAffineMeterOffsetAt code source leg channel := by
  apply SIQuantity.ext
  simp [finiteAffineMeterZeroReferenceAt, finiteAffineMeterRawAt]

theorem decodedFiniteAffineMeterGain_eq_generated
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    decodedFiniteAffineMeterGain
        (finiteAffineMeterZeroReferenceAt code source leg channel)
        (finiteAffineMeterSpanReferenceAt code source leg channel)
        (finiteAffineMeterSenseScaleAt source leg channel) =
      finiteAffineMeterGainAt code leg channel := by
  unfold decodedFiniteAffineMeterGain finiteAffineMeterZeroReferenceAt
    finiteAffineMeterSpanReferenceAt finiteAffineMeterRawAt
  simp only [SIQuantity.sub_value, SIQuantity.add_value,
    SIQuantity.smul_value, SIQuantity.zero_value, mul_zero, zero_add]
  field_simp [ne_of_gt (finiteAffineMeterSenseScale_pos source leg channel)]
  ring

theorem decodedFiniteAffineMeterNormalizedRead_eq_physical
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalVoltage : SIVolt) :
    decodedFiniteAffineMeterNormalizedRead
        (finiteAffineMeterZeroReferenceAt code source leg channel)
        (finiteAffineMeterSpanReferenceAt code source leg channel)
        (finiteAffineMeterRawAt
          code source leg channel physicalVoltage)
        (finiteAffineMeterSenseScaleAt source leg channel) =
      physicalVoltage.value /
        (finiteAffineMeterSenseScaleAt source leg channel).value := by
  unfold decodedFiniteAffineMeterNormalizedRead
  rw [decodedFiniteAffineMeterGain_eq_generated]
  unfold finiteAffineMeterZeroReferenceAt finiteAffineMeterRawAt
  simp only [SIQuantity.sub_value, SIQuantity.add_value,
    SIQuantity.smul_value, SIQuantity.zero_value, mul_zero, zero_add]
  have gainNonzero := ne_of_gt
    (finiteAffineMeterGain_pos code leg channel)
  have scaleNonzero := ne_of_gt
    (finiteAffineMeterSenseScale_pos source leg channel)
  field_simp [gainNonzero, scaleNonzero]
  ring

structure SourceGeneratedFiniteAffineVoltageMetrologyAt
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : Prop where
  gainPositive : 0 < finiteAffineMeterGainAt code leg channel
  scalePositive :
    0 < (finiteAffineMeterSenseScaleAt source leg channel).value
  zeroReferenceExact :
    finiteAffineMeterZeroReferenceAt code source leg channel =
      finiteAffineMeterOffsetAt code source leg channel
  decodedGainExact :
    decodedFiniteAffineMeterGain
        (finiteAffineMeterZeroReferenceAt code source leg channel)
        (finiteAffineMeterSpanReferenceAt code source leg channel)
        (finiteAffineMeterSenseScaleAt source leg channel) =
      finiteAffineMeterGainAt code leg channel
  calibratedOperationalExact : ∀ physicalVoltage,
    decodedFiniteAffineMeterNormalizedRead
        (finiteAffineMeterZeroReferenceAt code source leg channel)
        (finiteAffineMeterSpanReferenceAt code source leg channel)
        (finiteAffineMeterRawAt
          code source leg channel physicalVoltage)
        (finiteAffineMeterSenseScaleAt source leg channel) =
      physicalVoltage.value /
        (finiteAffineMeterSenseScaleAt source leg channel).value

theorem sourceGeneratedFiniteAffineVoltageMetrology
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    SourceGeneratedFiniteAffineVoltageMetrologyAt
      code source leg channel where
  gainPositive := finiteAffineMeterGain_pos code leg channel
  scalePositive := finiteAffineMeterSenseScale_pos source leg channel
  zeroReferenceExact := finiteAffineMeterZeroReference_eq_offset
    code source leg channel
  decodedGainExact := decodedFiniteAffineMeterGain_eq_generated
    code source leg channel
  calibratedOperationalExact :=
    decodedFiniteAffineMeterNormalizedRead_eq_physical
      code source leg channel

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.sourceGeneratedFiniteAffineVoltageMetrology
