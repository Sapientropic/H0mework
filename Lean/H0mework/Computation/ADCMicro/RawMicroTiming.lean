import H0mework.Computation.ADCMicro.RawMicroCorrectness

/-!
# Exact successful latency, separate from visible early rejection

The graph deadline is sufficient for every packet. For accepted packets it is
also the first completed-output tick: every actual transition consumes exactly
one outstanding unit of gate/control work. Acceptance is only a theorem-local
case split; the runtime continues to decide it from the raw packet.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

theorem finiteADCRawMicroAfterFor_residual
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (ticks : Nat) :
    finiteADCRawMicroResidual (finiteADCRawMicroAfterFor code lastTick packet ticks) =
      finiteADCRawMicroPacketResultFor code lastTick packet := by
  unfold finiteADCRawMicroAfterFor finiteADCRawMicroAfterWithProgram
  rw [finiteADCRawMicroResidual_after, finiteADCRawMicroResidual_bootFor]

theorem finiteADCRawMicroAfterFor_no_false_rejection
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (received : FiniteBinaryDrive)
    (accepted : finiteADCRawMicroPacketResultFor code lastTick packet = some received) (ticks : Nat) :
    finiteADCRawMicroOutput (finiteADCRawMicroAfterFor code lastTick packet ticks) ≠ some none := by
  intro rejected
  have actual := finiteADCRawMicroOutput_eq_residual_of_some _ none rejected
  rw [finiteADCRawMicroAfterFor_residual, accepted] at actual
  cases actual

theorem finiteADCRawMicroAfterFor_remaining_exact
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (received : FiniteBinaryDrive)
    (accepted : finiteADCRawMicroPacketResultFor code lastTick packet = some received) (ticks : Nat) :
    finiteADCRawMicroRemaining (finiteADCRawMicroAfterFor code lastTick packet ticks) =
      finiteADCRawMicroTicksFor code counterBits - ticks := by
  induction ticks with
  | zero =>
      simpa only [finiteADCRawMicroAfterFor, finiteADCRawMicroAfterWithProgram,
        Function.iterate_zero_apply, Nat.sub_zero] using
        finiteADCRawMicroBootFor_remaining code lastTick packet
  | succ ticks ih =>
      have nextNotRejected :
          finiteADCRawMicroOutput
            (finiteADCRawMicroStep (finiteADCRawMicroAfterFor code lastTick packet ticks)) ≠
              some none := by
        simpa only [finiteADCRawMicroAfterFor, finiteADCRawMicroAfterWithProgram,
          Function.iterate_succ_apply'] using
          finiteADCRawMicroAfterFor_no_false_rejection code lastTick packet received accepted
            (ticks + 1)
      simp only [finiteADCRawMicroAfterFor, finiteADCRawMicroAfterWithProgram,
        Function.iterate_succ_apply'] at ih nextNotRejected ⊢
      rw [finiteADCRawMicroRemaining_step_eq_of_not_rejected _ nextNotRejected, ih, Nat.sub_sub]

theorem finiteADCRawMicro_not_completed_earlyFor_of_accepted
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (received : FiniteBinaryDrive)
    (accepted : finiteADCRawMicroPacketResultFor code lastTick packet = some received)
    (ticks : Nat) (early : ticks < finiteADCRawMicroTicksFor code counterBits) :
    finiteADCRawMicroOutput (finiteADCRawMicroAfterFor code lastTick packet ticks) = none := by
  cases output : finiteADCRawMicroOutput (finiteADCRawMicroAfterFor code lastTick packet ticks) with
  | none => rfl
  | some result =>
      have zero := (finiteADCRawMicroRemaining_zero_iff_output _).mpr ⟨result, output⟩
      rw [finiteADCRawMicroAfterFor_remaining_exact code lastTick packet received accepted] at zero
      omega

/-- Source-identical installed programs cannot reject an accepted packet at an
intermediate tick. The acceptance value remains a theorem argument about the
code-level packet result, not installed runtime data. -/
theorem finiteADCRawMicroAfterWithProgram_no_false_rejection
    {code : FiniteADCResolutionCode}
    {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits)
    (received : FiniteBinaryDrive)
    (accepted : finiteADCRawMicroPacketResultFor code lastTick packet = some received)
    (ticks : Nat) :
    finiteADCRawMicroOutput
        (finiteADCRawMicroAfterWithProgram program lastTick packet ticks) ≠ some none := by
  rw [program.eq_compile]
  simpa only [finiteADCRawMicroAfterFor] using
    finiteADCRawMicroAfterFor_no_false_rejection code lastTick packet received accepted ticks

/-- For an accepted packet, every source-identical installed program first
exposes an output only at its graph-derived deadline. -/
theorem finiteADCRawMicro_not_completed_earlyWithProgram_of_accepted
    {code : FiniteADCResolutionCode}
    {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits)
    (received : FiniteBinaryDrive)
    (accepted : finiteADCRawMicroPacketResultFor code lastTick packet = some received)
    (ticks : Nat) (early : ticks < finiteADCRawMicroTicksWithProgram program) :
    finiteADCRawMicroOutput
        (finiteADCRawMicroAfterWithProgram program lastTick packet ticks) = none := by
  have earlyFor : ticks < finiteADCRawMicroTicksFor code counterBits := by
    simpa only [finiteADCRawMicroTicksWithProgram_eq] using early
  rw [program.eq_compile]
  simpa only [finiteADCRawMicroAfterFor] using
    finiteADCRawMicro_not_completed_earlyFor_of_accepted code lastTick packet received
      accepted ticks earlyFor

theorem finiteADCRawMicroAfter_residual
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :
    finiteADCRawMicroResidual (finiteADCRawMicroAfter source lastTick packet ticks) =
      receiveADC128WirePacket source lastTick packet :=
  (finiteADCRawMicroAfterFor_residual source.adcCode lastTick packet ticks).trans
    (finiteADCRawMicroPacketResult_eq_receive source lastTick packet)

theorem finiteADCRawMicroAfter_no_false_rejection
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (received : FiniteBinaryDrive)
    (accepted : receiveADC128WirePacket source lastTick packet = some received) (ticks : Nat) :
    finiteADCRawMicroOutput (finiteADCRawMicroAfter source lastTick packet ticks) ≠ some none :=
  finiteADCRawMicroAfterFor_no_false_rejection source.adcCode lastTick packet received
    ((finiteADCRawMicroPacketResult_eq_receive source lastTick packet).trans accepted) ticks

theorem finiteADCRawMicroAfter_remaining_exact
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (received : FiniteBinaryDrive)
    (accepted : receiveADC128WirePacket source lastTick packet = some received) (ticks : Nat) :
    finiteADCRawMicroRemaining (finiteADCRawMicroAfter source lastTick packet ticks) =
      finiteADCRawMicroTicks source counterBits - ticks :=
  finiteADCRawMicroAfterFor_remaining_exact source.adcCode lastTick packet received
    ((finiteADCRawMicroPacketResult_eq_receive source lastTick packet).trans accepted) ticks

theorem finiteADCRawMicro_not_completed_early_of_accepted
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (received : FiniteBinaryDrive)
    (accepted : receiveADC128WirePacket source lastTick packet = some received)
    (ticks : Nat) (early : ticks < finiteADCRawMicroTicks source counterBits) :
    finiteADCRawMicroOutput (finiteADCRawMicroAfter source lastTick packet ticks) = none :=
  finiteADCRawMicro_not_completed_earlyFor_of_accepted source.adcCode lastTick packet received
    ((finiteADCRawMicroPacketResult_eq_receive source lastTick packet).trans accepted) ticks early

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
