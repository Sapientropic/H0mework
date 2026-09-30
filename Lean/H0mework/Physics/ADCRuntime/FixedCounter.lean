import H0mework.Physics.ADCRuntime.UniformClock
import H0mework.Physics.ADCRuntime.Continuation

/-!
# One installed counter for all physical feedback frames

The boot initial and immutable hardware determine one finite packet format.
Every finite runtime current projects its already recorded ADC words and tick
into that format. No per-frame width reconfiguration or stored future trace
is used. The original parser and fixed-width energy circuit consume it.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Physical.Units.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

/-- The packet type depends on the boot configuration, never on the frame number. -/
abbrev FiniteADCPhysicalRuntimePacket
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) :=
  FiniteADCWirePacketAt hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)

/-- Changing only an analog initial condition cannot change this integer receiver. -/
theorem receiveADC128WirePacket_initial_independent
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (initial : FiniteDimensionedSeriesRLCPortState) {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketAt hardware counterBits) :
    receiveADC128WirePacket (finiteADCFixtureWithInitial hardware initial) lastTick packet =
      receiveADC128WirePacket hardware lastTick packet := by
  by_cases valid : validADCWirePacket hardware lastTick packet
  · have valid' : validADCWirePacket (finiteADCFixtureWithInitial hardware initial)
        lastTick packet := valid
    simp only [receiveADC128WirePacket, parseADCWirePacket, valid, valid', ↓reduceIte]
    rfl
  · have invalid' : ¬ validADCWirePacket (finiteADCFixtureWithInitial hardware initial)
        lastTick packet := valid
    simp [receiveADC128WirePacket, parseADCWirePacket, valid, invalid']

/-- The old stored-data projection works at any installed width that contains its tick. -/
theorem unpack_recordedADCWirePacket_current
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) {counterBits : Nat}
    (fits : current.val.sampleTick < 2 ^ counterBits) :
    unpackADCWirePacket (finiteADCPhysicalCurrentSource current)
        (recordedADCWirePacket (finiteADCPhysicalCurrentSource current) current.val
          (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
            current.property) fits) =
      compiledADCDigitalSample (finiteADCPhysicalCurrentSource current) current.val.drive := by
  apply FiniteADCDigitalSample.ext
  · exact congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.sampleTick
      current.property
  · funext frame leg channel
    rw [show
      (unpackADCWirePacket (finiteADCPhysicalCurrentSource current)
        (recordedADCWirePacket (finiteADCPhysicalCurrentSource current) current.val
          (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
            current.property) fits)).wordsAt frame leg channel =
      ⟨(current.val.adcWordAt frame leg channel).val, by
        have codeExact := congrArg
          FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.property
        change current.val.adcCode = (finiteADCPhysicalCurrentSource current).adcCode at codeExact
        simpa only [codeExact] using (current.val.adcWordAt frame leg channel).property⟩
      from decode_packADCWord _ _]
    apply Subtype.ext
    exact congrArg (fun run => (run.adcWordAt frame leg channel).val) current.property

theorem recordedADCWirePacket_current_valid
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) {counterBits : Nat}
    (fits : current.val.sampleTick < 2 ^ counterBits)
    (lastTick : Nat) (inSchedule : current.val.sampleTick ≤ lastTick) :
    validADCWirePacket (finiteADCPhysicalCurrentSource current) lastTick
      (recordedADCWirePacket (finiteADCPhysicalCurrentSource current) current.val
        (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
          current.property) fits) :=
  ⟨inSchedule, fun _ _ _ => packADCWord_valid _ _⟩

theorem receive_recordedADCWirePacket_current
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) {counterBits : Nat}
    (fits : current.val.sampleTick < 2 ^ counterBits)
    (lastTick : Nat) (inSchedule : current.val.sampleTick ≤ lastTick) :
    receiveADC128WirePacket (finiteADCPhysicalCurrentSource current) lastTick
      (recordedADCWirePacket (finiteADCPhysicalCurrentSource current) current.val
        (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
          current.property) fits) = some current.val.drive := by
  simp [receiveADC128WirePacket, parseADCWirePacket,
    recordedADCWirePacket_current_valid current fits lastTick inSchedule,
    unpack_recordedADCWirePacket_current,
    validADCEnergyCalibration_compiled, decodeFiniteADC128EnergySample_compiled]

noncomputable section

/-- Project the actual iterated current into the one preinstalled format. -/
def finiteADCPhysicalRuntimePacketAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) :
    FiniteADCPhysicalRuntimePacket hardware bootInitial :=
  let current := finiteADCPhysicalCurrentAfter
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame
  recordedADCWirePacket hardware current.val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
      current.property)
    (finiteADCPhysicalIterate_sampleTick_lt_fixedCapacity hardware bootInitial bootDrive frame)

theorem finiteADCPhysicalRuntimePacketAt_tick
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) :
    (finiteADCPhysicalRuntimePacketAt hardware bootInitial bootDrive frame).1.val =
      (finiteADCPhysicalCurrentAfter
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame).val.sampleTick := rfl

theorem finiteADCPhysicalRuntimePacketAt_received
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) :
    receiveADC128WirePacket hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
        (finiteADCPhysicalRuntimePacketAt hardware bootInitial bootDrive frame) =
      some (finiteADCPhysicalCurrentAfter
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame).val.drive := by
  let current := finiteADCPhysicalCurrentAfter
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame
  have received := receive_recordedADCWirePacket_current current
    (finiteADCPhysicalIterate_sampleTick_lt_fixedCapacity hardware bootInitial bootDrive frame)
    (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
    (finiteADCPhysicalIterate_sampleTick_le_runtimeMax hardware bootInitial bootDrive frame)
  change receiveADC128WirePacket (finiteADCFixtureWithInitial hardware current.val.initial)
      (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
      (finiteADCPhysicalRuntimePacketAt hardware bootInitial bootDrive frame) =
        some current.val.drive at received
  rw [receiveADC128WirePacket_initial_independent] at received
  exact received

/-- Feedback now consumes the one installed packet format and one installed bound. -/
def finiteADCPhysicalRuntimeFixedFeedbackAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) : FiniteBinaryDrive :=
  match receiveADC128WirePacket hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
      (finiteADCPhysicalRuntimePacketAt hardware bootInitial bootDrive frame) with
  | some received => fun channel => !(received channel)
  | none => uniformBinaryDrive false

theorem finiteADCPhysicalRuntimeFixedFeedbackAt_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) :
    finiteADCPhysicalRuntimeFixedFeedbackAt hardware bootInitial bootDrive frame =
      finiteADCPhysicalFeedback (finiteADCPhysicalCurrentAfter
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame) := by
  unfold finiteADCPhysicalRuntimeFixedFeedbackAt
  rw [finiteADCPhysicalRuntimePacketAt_received, finiteADCPhysicalFeedback_exact]

/-- The new physical run is generated from the fixed-counter receiver, not
merely assigned an equal packet after an unrelated transition. -/
def finiteADCPhysicalRuntimeFixedNextAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) : FiniteADCPhysicalRuntimeCurrent hardware :=
  let current := finiteADCPhysicalCurrentAfter
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame
  startFiniteADCPhysicalRuntime hardware (finiteADCPhysicalEndpoint current)
    (finiteADCPhysicalRuntimeFixedFeedbackAt hardware bootInitial bootDrive frame)

theorem finiteADCPhysicalRuntimeFixedNextAt_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) :
    finiteADCPhysicalRuntimeFixedNextAt hardware bootInitial bootDrive frame =
      finiteADCPhysicalCurrentAfter
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) (frame + 1) := by
  unfold finiteADCPhysicalRuntimeFixedNextAt
  rw [finiteADCPhysicalRuntimeFixedFeedbackAt_commutes,
    finiteADCPhysicalCurrentAfter_succ]
  rfl

theorem finiteADCPhysicalRuntimeFixedNextAt_no_reset
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frame : Nat) :
    finiteADCPhysicalStateAt
        (finiteADCPhysicalRuntimeFixedNextAt hardware bootInitial bootDrive frame) 0 =
      finiteADCPhysicalEndpoint (finiteADCPhysicalCurrentAfter
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frame) := by
  rw [finiteADCPhysicalRuntimeFixedNextAt_commutes]
  exact finiteADCPhysicalContinuation_no_reset _ frame

/-- Full finite packet capacity, fixed for all frames and all initial commands. -/
theorem finiteADCPhysicalRuntimePacket_card
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) :
    Fintype.card (FiniteADCPhysicalRuntimePacket hardware bootInitial) =
      2 ^ (finiteADCPhysicalRuntimeClockBits hardware bootInitial +
        60 * adcWordBits hardware.adcCode) :=
  finiteADCWirePacketFor_card hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial)

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
