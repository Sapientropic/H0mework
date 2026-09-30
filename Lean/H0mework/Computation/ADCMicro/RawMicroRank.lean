import H0mework.Computation.ADCMicro.RawMicroMachine
import H0mework.Computation.ADCMicro.MicroCountdown

/-! # The installed graph schedule completes the actual microcontroller -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

theorem finiteADCRawMicroBootFor_remaining
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroRemaining (finiteADCRawMicroBootFor code lastTick packet) =
      finiteADCRawMicroTicksFor code counterBits := by
  simp only [finiteADCRawMicroBootFor, finiteADCRawMicroBootWithProgram,
    finiteADCRawMicroRemaining, finiteADCRawProgramPacketCall,
    aigOwnedProgressBoot_ticks, Nat.sub_zero, finiteADCRawMicroTicksFor, finiteADCRawPhaseCommitTicks]

theorem finiteADCRawMicroTicksFor_gt_macro
    (code : FiniteADCResolutionCode) (counterBits : Nat) :
    8 < finiteADCRawMicroTicksFor code counterBits := by
  unfold finiteADCRawMicroTicksFor finiteADCRawMicroCalibrationTicksFor finiteADCRawMicroDifferenceTicks
    finiteADCRawMicroSquareTicks finiteADCRawMicroProductTicks finiteADCRawMicroSumTicks
    finiteADCRawMicroScaleTicks finiteADCRawMicroCompareTicks
    finiteADCRawPhaseCommitTicks finiteADCRawSpanAndControlTicks finiteADCRawFinalCompareControlTicks
  omega

theorem finiteADCRawMicroTicksFor_pos
    (code : FiniteADCResolutionCode) (counterBits : Nat) :
    0 < finiteADCRawMicroTicksFor code counterBits :=
  Nat.lt_trans (by decide) (finiteADCRawMicroTicksFor_gt_macro code counterBits)

theorem finiteADCRawMicroRemaining_zero_iff_output
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat} (state : FiniteADCRawMicroStateFor code counterBits lastTick) :
    finiteADCRawMicroRemaining state = 0 ↔ ∃ result, finiteADCRawMicroOutput state = some result := by
  cases state <;> simp only [finiteADCRawMicroRemaining, finiteADCRawMicroOutput]
  all_goals simp

theorem finiteADCRawMicroRemaining_zero_stable
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat} (state : FiniteADCRawMicroStateFor code counterBits lastTick)
    (zero : finiteADCRawMicroRemaining state = 0) :
    finiteADCRawMicroRemaining (finiteADCRawMicroStep state) = 0 := by
  cases state <;> simp only [finiteADCRawMicroRemaining] at zero
  all_goals try omega
  rfl

theorem finiteADCRawMicroRemaining_step_lt
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat} (state : FiniteADCRawMicroStateFor code counterBits lastTick)
    (positive : 0 < finiteADCRawMicroRemaining state) :
    finiteADCRawMicroRemaining (finiteADCRawMicroStep state) <
      finiteADCRawMicroRemaining state := by
  have packetSize := (compileFiniteADCRawInstalledProgram code counterBits).packet_size_eq
  have calibrationSize := (compileFiniteADCRawInstalledProgram code counterBits).calibration_size_eq
  cases state with
  | packet raw current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · split <;>
          simp only [finiteADCRawMicroRemaining, finiteADCRawProgramCalibrationCall,
            aigOwnedProgressBoot_ticks, Nat.sub_zero, finiteADCRawMicroCalibrationTicksFor,
            finiteADCRawPhaseCommitTicks] <;> omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedProgressStep_ticks]
        omega
  | calibration checked current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · split <;>
          simp only [finiteADCRawMicroRemaining, finiteADCRawDifferencePhaseCall,
            aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroDifferenceTicks,
            finiteADCRawPhaseCommitTicks] <;> omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedProgressStep_ticks]
        omega
  | difference checked current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawSquarePhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroSquareTicks,
          finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | square input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawProductPhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroProductTicks,
          finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | product input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawSumPhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroSumTicks,
          finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | sum input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawScalePhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroScaleTicks,
          finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | scale input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawSignedComparePhaseCall,
          finiteADCRawUnsignedComparePhaseCall, aigOwnedBatchBoot_ticks, Nat.sub_zero,
          finiteADCRawMicroCompareTicks, finiteADCRawComparePhaseGraphTicks,
          finiteADCRawSpanAndControlTicks, finiteADCRawFinalCompareControlTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | compare input signedCurrent unsignedCurrent =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | finalAnd spanAnd input unsignedCurrent complete =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram,
        finiteADCRawMicroRemaining]
      decide
  | done result =>
      simp only [finiteADCRawMicroRemaining] at positive
      omega

/-- Every non-rejection transition spends exactly one outstanding tick. -/
theorem finiteADCRawMicroRemaining_step_eq_of_not_rejected
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat} (state : FiniteADCRawMicroStateFor code counterBits lastTick)
    (notRejected : finiteADCRawMicroOutput (finiteADCRawMicroStep state) ≠ some none) :
    finiteADCRawMicroRemaining (finiteADCRawMicroStep state) =
      finiteADCRawMicroRemaining state - 1 := by
  have packetSize := (compileFiniteADCRawInstalledProgram code counterBits).packet_size_eq
  have calibrationSize := (compileFiniteADCRawInstalledProgram code counterBits).calibration_size_eq
  cases state with
  | packet raw current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram] at notRejected ⊢
      split
      · split
        · simp only [finiteADCRawMicroRemaining, finiteADCRawProgramCalibrationCall,
            aigOwnedProgressBoot_ticks, Nat.sub_zero, finiteADCRawMicroCalibrationTicksFor,
            finiteADCRawPhaseCommitTicks]
          omega
        · simp_all [finiteADCRawMicroOutput, ← packetSize]
      · simp only [finiteADCRawMicroRemaining, aigOwnedProgressStep_ticks]
        omega
  | calibration checked current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram] at notRejected ⊢
      split
      · split
        · simp only [finiteADCRawMicroRemaining, finiteADCRawDifferencePhaseCall,
            aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroDifferenceTicks,
            finiteADCRawPhaseCommitTicks]
          omega
        · simp_all [finiteADCRawMicroOutput, ← calibrationSize]
      · simp only [finiteADCRawMicroRemaining, aigOwnedProgressStep_ticks]
        omega
  | difference checked current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawSquarePhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroSquareTicks, finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | square input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawProductPhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroProductTicks, finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | product input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawSumPhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroSumTicks, finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | sum input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawScalePhaseCall,
          aigOwnedBatchBoot_ticks, Nat.sub_zero, finiteADCRawMicroScaleTicks, finiteADCRawPhaseCommitTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | scale input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining, finiteADCRawSignedComparePhaseCall,
          finiteADCRawUnsignedComparePhaseCall, aigOwnedBatchBoot_ticks, Nat.sub_zero,
          finiteADCRawMicroCompareTicks, finiteADCRawComparePhaseGraphTicks,
          finiteADCRawSpanAndControlTicks, finiteADCRawFinalCompareControlTicks]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | compare input signedCurrent unsignedCurrent =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroRemaining]
        omega
      · simp only [finiteADCRawMicroRemaining, aigOwnedBatchStep_ticks]
        omega
  | finalAnd spanAnd input unsignedCurrent complete => rfl
  | done result => rfl

theorem finiteADCRawMicroAfterFor_remaining_zero
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroRemaining
      (finiteADCRawMicroAfterFor code lastTick packet (finiteADCRawMicroTicksFor code counterBits)) = 0 :=
  finiteADCMicroCountdown_eq_zero_of_le finiteADCRawMicroStep finiteADCRawMicroRemaining
    finiteADCRawMicroRemaining_zero_stable finiteADCRawMicroRemaining_step_lt
    (finiteADCRawMicroBootFor code lastTick packet) _ (le_of_eq (finiteADCRawMicroBootFor_remaining _ _ _))

theorem finiteADCRawMicroBoot_remaining
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawMicroRemaining (finiteADCRawMicroBoot source lastTick packet) =
      finiteADCRawMicroTicks source counterBits :=
  finiteADCRawMicroBootFor_remaining source.adcCode lastTick packet

theorem finiteADCRawMicroTicks_gt_macro
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (counterBits : Nat) :
    8 < finiteADCRawMicroTicks source counterBits :=
  finiteADCRawMicroTicksFor_gt_macro source.adcCode counterBits

theorem finiteADCRawMicroTicks_pos
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (counterBits : Nat) :
    0 < finiteADCRawMicroTicks source counterBits :=
  finiteADCRawMicroTicksFor_pos source.adcCode counterBits

theorem finiteADCRawMicroAfter_remaining_zero
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawMicroRemaining
      (finiteADCRawMicroAfter source lastTick packet (finiteADCRawMicroTicks source counterBits)) = 0 :=
  finiteADCRawMicroAfterFor_remaining_zero source.adcCode lastTick packet

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
