import H0mework.Computation.ADC.Word
import H0mework.Computation.ADCWire.DigitalRepresentation
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Source-generated finite clock and wire packet

The fixed source schedules a finite family of independently addressed commands.
Its maximum generated tick determines the counter width. Payload words use
explicit offset-binary arithmetic. Parsing rejects unused ADC codes and clock
headers beyond the source schedule; successful parsing does not certify that
an arbitrary packet was emitted by the circuit.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

noncomputable section

/-- This is the finite admitted command census, not a preinstalled future sequence. -/
def maxADCSampleTick (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Nat :=
  Finset.univ.sup (finiteADCClockedSampleTick source)

def adcClockBits (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Nat :=
  Nat.log 2 (maxADCSampleTick source) + 1

theorem adcSampleTick_le_max
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    finiteADCClockedSampleTick source drive ≤ maxADCSampleTick source :=
  Finset.le_sup (Finset.mem_univ drive)

theorem maxADCSampleTick_lt_capacity
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    maxADCSampleTick source < 2 ^ adcClockBits source :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) _

theorem adcSampleTick_no_counter_overflow
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    finiteADCClockedSampleTick source drive < 2 ^ adcClockBits source :=
  lt_of_le_of_lt (adcSampleTick_le_max source drive) (maxADCSampleTick_lt_capacity source)

/-- One finite counter header and sixty finite ADC payload words. The counter
width is installed configuration, independent of the current initial state. -/
abbrev FiniteADCWirePacketFor (code : FiniteADCResolutionCode) (counterBits : Nat) :=
  QuantizedWord counterBits ×
    (FiniteAffineMeterFrame → SynchronousSenseLeg → FiniteEmbodimentChannel →
      QuantizedWord (adcWordBits code))

/-- The physical packet is the same code-indexed carrier at its source's ADC coordinate. -/
abbrev FiniteADCWirePacketAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (counterBits : Nat) :=
  FiniteADCWirePacketFor source.adcCode counterBits

abbrev FiniteADCWirePacket (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :=
  FiniteADCWirePacketAt source (adcClockBits source)

def packADCExecution
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : FiniteADCWirePacket source :=
  (⟨finiteADCClockedSampleTick source drive, adcSampleTick_no_counter_overflow source drive⟩,
    fun frame leg channel => packADCWord source.adcCode
      ((compiledADCDigitalSample source drive).wordsAt frame leg channel))

end

/-- Decoding the arithmetic packet does not read a source command or analog state. -/
def unpackADCWirePacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (packet : FiniteADCWirePacketAt source counterBits) : FiniteADCDigitalSample source where
  sampleTick := packet.1.val
  wordsAt := fun frame leg channel => decodeADCWord source.adcCode (packet.2 frame leg channel)

def validADCWirePacketFor (code : FiniteADCResolutionCode)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) : Prop :=
  packet.1.val ≤ lastTick ∧
    ∀ frame leg channel, validADCWord code (packet.2 frame leg channel)

instance (code : FiniteADCResolutionCode) {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    Decidable (validADCWirePacketFor code lastTick packet) :=
  inferInstanceAs (Decidable (_ ∧ _))

def validADCWirePacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) : Prop :=
  validADCWirePacketFor source.adcCode lastTick packet

instance (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    Decidable (validADCWirePacket source lastTick packet) :=
  inferInstanceAs (Decidable (validADCWirePacketFor source.adcCode lastTick packet))

/-- The numeric schedule bound is explicit configuration data, so parsing does not
compute the real-valued source schedule. The producer supplies its exact bound below. -/
def parseADCWirePacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    Option (FiniteADCDigitalSample source) :=
  if validADCWirePacket source lastTick packet then some (unpackADCWirePacket source packet) else none

noncomputable section

theorem packADCExecution_valid
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    validADCWirePacket source (maxADCSampleTick source) (packADCExecution source drive) :=
  ⟨adcSampleTick_le_max source drive, fun _ _ _ => packADCWord_valid source.adcCode _⟩

@[simp] theorem unpack_packADCExecution
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    unpackADCWirePacket source (packADCExecution source drive) =
      compiledADCDigitalSample source drive := by
  apply FiniteADCDigitalSample.ext
  · rfl
  · funext frame leg channel
    exact decode_packADCWord source.adcCode _

@[simp] theorem parse_packADCExecution
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    parseADCWirePacket source (maxADCSampleTick source) (packADCExecution source drive) =
      some (compiledADCDigitalSample source drive) := by
  simp [parseADCWirePacket, packADCExecution_valid]

theorem parseADCWirePacket_rejects_invalid
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits)
    (invalid : ¬ validADCWirePacket source lastTick packet) :
    parseADCWirePacket source lastTick packet = none := by
  simp [parseADCWirePacket, invalid]

/-- Decoded wire data retains the physical exact-readback theorem. -/
theorem decode_packADCExecution
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    decodeDigitalSample source (unpackADCWirePacket source (packADCExecution source drive)) =
      drive := by
  rw [unpack_packADCExecution, decodeDigitalSample_compiled]

theorem packADCExecution_injective
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Function.Injective (packADCExecution source) :=
  Function.LeftInverse.injective (f := packADCExecution source)
    (g := fun packet => decodeDigitalSample source (unpackADCWirePacket source packet))
    (decode_packADCExecution source)

def adcWirePacketBits (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Nat :=
  adcClockBits source + 60 * adcWordBits source.adcCode

theorem finiteADCWirePacketFor_card (code : FiniteADCResolutionCode) (counterBits : Nat) :
    Fintype.card (FiniteADCWirePacketFor code counterBits) = 2 ^ (counterBits + 60 * adcWordBits code) := by
  simp only [FiniteADCWirePacketFor, QuantizedWord,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  have frames : Fintype.card FiniteAffineMeterFrame = 3 := by decide
  have legs : Fintype.card SynchronousSenseLeg = 2 := by decide
  have channels : Fintype.card FiniteEmbodimentChannel = 10 := by decide
  rw [frames, legs, channels]
  simp only [← pow_mul, pow_add]
  congr 2
  omega

theorem finiteADCWirePacket_card
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Fintype.card (FiniteADCWirePacket source) = 2 ^ adcWirePacketBits source :=
  finiteADCWirePacketFor_card source.adcCode (adcClockBits source)

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
