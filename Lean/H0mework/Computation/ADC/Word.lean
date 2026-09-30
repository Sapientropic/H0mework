import H0mework.Physics.Measurement.ADC
import H0mework.Cognition.Precision.Disposition

/-!
# Explicit fixed-width encoding of bounded ADC symbols

Signed interval symbols are offset into 23-, 24-, or 25-bit words.
Decoding subtracts that offset and clamps unused codes. Validity is a
separate decidable range test; it is exactly the round-trip criterion.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

/-- Fixed binary widths large enough for every signed ADC code, including both end points. -/
def adcWordBits : FiniteADCResolutionCode → Nat
  | .coarse => 23
  | .medium => 24
  | .fine => 25

theorem adcWord_offset_nonnegative (code : FiniteADCResolutionCode)
    (word : FiniteADCWord code) :
    0 ≤ word.val + 16 * finiteADCGridDenominator code := by
  have lower := word.property.1
  omega

/-- Offset-binary encoding; this is an arithmetic map, not an arbitrary finite equivalence. -/
def packADCWord (code : FiniteADCResolutionCode)
    (word : FiniteADCWord code) : QuantizedWord (adcWordBits code) :=
  ⟨(word.val + 16 * finiteADCGridDenominator code).toNat, by
    rw [Int.toNat_lt (adcWord_offset_nonnegative code word)]
    have upper := word.property.2
    cases code <;>
      norm_num [finiteADCGridDenominator, adcWordBits] at upper ⊢ <;> omega⟩

/-- Binary encodings above the ADC's last offset code are unused. -/
def validADCWord (code : FiniteADCResolutionCode)
    (bits : QuantizedWord (adcWordBits code)) : Prop :=
  (bits.val : Int) ≤ 32 * finiteADCGridDenominator code

instance (code : FiniteADCResolutionCode) (bits : QuantizedWord (adcWordBits code)) :
    Decidable (validADCWord code bits) := inferInstanceAs (Decidable (_ ≤ _))

/-- Total arithmetic symbol decoder; callers separately observe the validity test. -/
def decodeADCWord (code : FiniteADCResolutionCode)
    (bits : QuantizedWord (adcWordBits code)) : FiniteADCWord code :=
  ⟨min ((bits.val : Int) - 16 * finiteADCGridDenominator code)
      (16 * finiteADCGridDenominator code), by
    have positive := finiteADCGridDenominator_pos code
    constructor
    · apply le_min <;> omega
    · exact min_le_right _ _⟩

theorem packADCWord_valid (code : FiniteADCResolutionCode) (word : FiniteADCWord code) :
    validADCWord code (packADCWord code word) := by
  unfold validADCWord packADCWord
  rw [Int.toNat_of_nonneg (adcWord_offset_nonnegative code word)]
  have upper := word.property.2
  omega

theorem decode_packADCWord (code : FiniteADCResolutionCode) (word : FiniteADCWord code) :
    decodeADCWord code (packADCWord code word) = word := by
  apply Subtype.ext
  change min (((word.val + 16 * finiteADCGridDenominator code).toNat : Int) -
      16 * finiteADCGridDenominator code) (16 * finiteADCGridDenominator code) = word.val
  rw [Int.toNat_of_nonneg (adcWord_offset_nonnegative code word)]
  simp only [add_sub_cancel_right, min_eq_left word.property.2]

theorem pack_decodeADCWord_of_valid (code : FiniteADCResolutionCode)
    (bits : QuantizedWord (adcWordBits code)) (valid : validADCWord code bits) :
    packADCWord code (decodeADCWord code bits) = bits := by
  apply Fin.ext
  have signedLe : (bits.val : Int) - 16 * finiteADCGridDenominator code ≤
      16 * finiteADCGridDenominator code := by
    unfold validADCWord at valid
    omega
  simp only [packADCWord, decodeADCWord, min_eq_left signedLe,
    sub_add_cancel, Int.toNat_natCast]

theorem validADCWord_iff_roundTrip (code : FiniteADCResolutionCode)
    (bits : QuantizedWord (adcWordBits code)) :
    validADCWord code bits ↔ packADCWord code (decodeADCWord code bits) = bits := by
  constructor
  · exact pack_decodeADCWord_of_valid code bits
  · intro roundTrip
    rw [← roundTrip]
    exact packADCWord_valid code _

/-- No silent saturation enters an accepted finite symbol parse. -/
def parseADCWord (code : FiniteADCResolutionCode)
    (bits : QuantizedWord (adcWordBits code)) : Option (FiniteADCWord code) :=
  if validADCWord code bits then some (decodeADCWord code bits) else none

@[simp] theorem parse_packADCWord (code : FiniteADCResolutionCode)
    (word : FiniteADCWord code) :
    parseADCWord code (packADCWord code word) = some word := by
  simp [parseADCWord, packADCWord_valid, decode_packADCWord]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
