import H0mework.Computation.ADCGates.Gate128Correctness
import H0mework.Computation.ADCWire.EnergyWireReceiver

/-!
# Raw offset-binary admission and differences

Range admission removes the decoder's upper clamp. The common offset then
cancels from calibration order and from every 128-bit difference. The whole
packet theorem consumes the range guards before using either cancellation.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

theorem finiteADCDecodedRawValue_of_valid
    (code : FiniteADCResolutionCode) (raw : QuantizedWord (adcWordBits code))
    (valid : validADCWord code raw) :
    (decodeADCWord code raw).val = (raw.val : Int) - 16 * finiteADCGridDenominator code := by
  have unclamped : (raw.val : Int) - 16 * finiteADCGridDenominator code ≤
      16 * finiteADCGridDenominator code := by
    unfold validADCWord at valid
    omega
  exact min_eq_left unclamped

theorem finiteADCDecodedSpanPositive_iff_raw_lt
    (code : FiniteADCResolutionCode) (zero span : QuantizedWord (adcWordBits code))
    (zeroValid : validADCWord code zero) (spanValid : validADCWord code span) :
    0 < (decodeADCWord code span).val - (decodeADCWord code zero).val ↔ zero.val < span.val := by
  rw [finiteADCDecodedRawValue_of_valid code span spanValid,
    finiteADCDecodedRawValue_of_valid code zero zeroValid]
  omega

def finiteADCRawPacketAdmission
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) : Prop :=
  packet.1.val ≤ lastTick ∧
    (∀ frame leg channel, validADCWord source.adcCode (packet.2 frame leg channel)) ∧
    (∀ leg channel,
      (packet.2 .zeroReference leg channel).val < (packet.2 .spanReference leg channel).val)

instance (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    Decidable (finiteADCRawPacketAdmission source lastTick packet) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Unconditional whole-packet exactness, including every invalid input. -/
theorem finiteADCRawPacketAdmission_iff
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawPacketAdmission source lastTick packet ↔
      validADCWirePacket source lastTick packet ∧
        validADCEnergyCalibration (unpackADCWirePacket source packet) := by
  constructor
  · rintro ⟨tick, words, spans⟩
    refine ⟨⟨tick, words⟩, fun leg channel => ?_⟩
    exact (finiteADCDecodedSpanPositive_iff_raw_lt source.adcCode _ _
      (words .zeroReference leg channel) (words .spanReference leg channel)).mpr (spans leg channel)
  · rintro ⟨packetValid, calibrated⟩
    refine ⟨packetValid.1, packetValid.2, fun leg channel => ?_⟩
    exact (finiteADCDecodedSpanPositive_iff_raw_lt source.adcCode _ _
      (packetValid.2 .zeroReference leg channel)
      (packetValid.2 .spanReference leg channel)).mp (calibrated leg channel)

/-- Gate arithmetic may consume raw words directly once the actual admission
has generated their validity proofs. No offset subtraction is needed at runtime. -/
theorem finiteADCRawDifference128_eq_decodedDifference
    (code : FiniteADCResolutionCode) (left right : QuantizedWord (adcWordBits code))
    (leftValid : validADCWord code left) (rightValid : validADCWord code right) :
    finiteADC128GateSub (BitVec.ofNat 128 left.val) (BitVec.ofNat 128 right.val) =
      finiteADCBitVectorDifference128 (decodeADCWord code left) (decodeADCWord code right) := by
  rw [finiteADC128GateSub_eq_sub, finiteADCBitVectorDifference128_eq_ofInt,
    finiteADCDecodedRawValue_of_valid code left leftValid,
    finiteADCDecodedRawValue_of_valid code right rightValid,
    ← BitVec.ofInt_natCast 128 left.val, ← BitVec.ofInt_natCast 128 right.val,
    sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  congr 1
  omega

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
