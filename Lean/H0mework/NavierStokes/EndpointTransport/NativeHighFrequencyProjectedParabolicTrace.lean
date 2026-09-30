import H0mework.NavierStokes.EndpointTransport.CofinalNonlinearNegativeOneEuclideanBalance
import H0mework.NavierStokes.PairRestart.PairOccurrenceWork
import H0mework.NavierStokes.Restart.FiniteTimeHighFrequencyTailDivergence
import H0mework.NavierStokes.Restart.SymmetricVelocityMultiplierGapTransport

/-!
# Native high-frequency projected parabolic trace

The complete tangent/viscous cross trace of one actual whole-PDE receipt,
after subtracting the canonical finite-cube trace, is exactly the omitted
whole-vorticity boundary trace.  The identity telescopes on every `Ico` of
the original whole-restart run; no cofinal selector or boundary relation is
part of its theorem mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSymmetricVelocityMultiplierGapTransport
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage
namespace FullFrameBoundaryVorticityNativeHighFrequencyProjectedParabolicTrace

open FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

variable {nu : Viscosity}

/-- The complete tangent/viscous cross trace minus the canonical finite-cube
trace of the identical unforced receipt. -/
def receiptHighFrequencyProjectedParabolicTrace
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) : Real :=
  2 * RCLike.re (inner ℂ
      (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
      (puncturedEuclideanSpaceTimeState
        (receiptViscousNegativeOneState receipt))) -
    nu.coeff *
      actualWholeFiniteNetWork receipt (wholeRestartModes radius)

/-- The projected parabolic trace is exactly the change of omitted
whole-vorticity mass on the same actual receipt. -/
theorem receiptHighFrequencyProjectedParabolicTrace_eq_boundaryComplement
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    receiptHighFrequencyProjectedParabolicTrace receipt radius =
      nu.coeff *
        (wholeVorticityEuclideanMass
            (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath
                  ⟨requestedTime,
                    ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
              receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection (wholeRestartModes radius)
                initialState - initialState)) := by
  unfold receiptHighFrequencyProjectedParabolicTrace
  rw [receipt_puncturedEuclidean_cross_eq_boundary,
    actualWholeFiniteNetWork_eq_terminal_sub_initial,
    finiteStateVorticityCoefficientEnstrophy_eq_projectionMass,
    finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
  rw [wholeVorticityEuclideanMass_eq_projection_add_complement
      (wholeRestartModes radius)
      (receipt.wholePath
        ⟨requestedTime,
          ⟨receipt.requestedTimePos.le, le_rfl⟩⟩),
    wholeVorticityEuclideanMass_eq_projection_add_complement
      (wholeRestartModes radius) initialState]
  ring

/-- The omitted boundary trace is paid row-for-row by the same receipt's
outside pair incidence minus its literal viscous debit.  The complement is
not a free observer loss: its outputs, input-pair table, and time integral
all come from the original whole-PDE write. -/
theorem
    receiptHighFrequencyProjectedParabolicTrace_eq_complementPair_sub_viscous
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    receiptHighFrequencyProjectedParabolicTrace receipt radius =
      nu.coeff *
        ∑' output : NonzeroIntegerWavevector,
          if output.1 ∈ wholeRestartModes radius then 0
          else
            (∑' first : IntegerWavevector,
                actualWholePairOccurrenceWork receipt output.1 first) -
              actualWholeRowViscousPayment receipt output.1 := by
  rw [receiptHighFrequencyProjectedParabolicTrace_eq_boundaryComplement]
  congr 1
  have terminalZero :
      receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ 0 = 0 :=
    receipt.wholePath_zero_row _
  have initialZero : initialState 0 = 0 := by
    rw [← receipt.wholePath_initial]
    exact receipt.wholePath_zero_row _
  have zeroNotMem :
      (0 : IntegerWavevector) ∉ wholeRestartModes radius :=
    zero_not_mem_wholeRestartModes radius
  have terminalComplementZero :
      (complexSharpSupportProjection (wholeRestartModes radius)
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) 0 = 0 := by
    simp [complexSharpSupportProjection_apply, zeroNotMem, terminalZero]
  have initialComplementZero :
      (complexSharpSupportProjection (wholeRestartModes radius)
            initialState - initialState) 0 = 0 := by
    simp [complexSharpSupportProjection_apply, zeroNotMem, initialZero]
  rw [← puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
      _ terminalComplementZero,
    ← puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
      _ initialComplementZero]
  unfold puncturedWholeVorticityEuclideanMass
  rw [← Summable.tsum_sub
    (summable_puncturedWholeVorticityEuclideanMass _)
    (summable_puncturedWholeVorticityEuclideanMass _)]
  apply tsum_congr
  intro output
  by_cases outputMem : output.1 ∈ wholeRestartModes radius
  · simp [complexSharpSupportProjection_apply, outputMem,
      complexCoordinateAmplitudeSq]
  · rw [if_neg outputMem]
    have pairSubViscousEq :
        (∑' first : IntegerWavevector,
            actualWholePairOccurrenceWork receipt output.1 first) -
            actualWholeRowViscousPayment receipt output.1 =
          complexCoordinateAmplitudeSq
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ output.1) -
            complexCoordinateAmplitudeSq (initialState output.1) := by
      rw [tsum_actualWholePairOccurrenceWork_eq_rowPreQuotientWork
          receipt output.1 output.2,
        actualWholeRowPreQuotientWork_eq_bilinearWork,
        ← actualWholeRowNonlinearWork_eq_bilinearWork]
      unfold actualWholeRowNonlinearWork
      rw [actualWholeRowNetWork_eq_terminal_sub_initial]
      ring
    rw [pairSubViscousEq]
    simp [complexSharpSupportProjection_apply, outputMem,
      complexCoordinateAmplitudeSq]

/-- The same omitted boundary trace, now resolved on every complete input
swap orbit, is the outside reflected keep plus its forced multiplier-gap
trace after the literal viscous debit.  This is an equality on the original
receipt; it does not turn observer loss into a new law or settlement. -/
theorem
    receiptHighFrequencyProjectedParabolicTrace_eq_half_complementReflectedTransport_sub_viscous
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    receiptHighFrequencyProjectedParabolicTrace receipt radius =
      (nu.coeff / 2) *
        ∑' output : NonzeroIntegerWavevector,
          if output.1 ∈ wholeRestartModes radius then 0
          else
            (∑' first : IntegerWavevector,
                (actualWholeSymmetricVelocityReflectedKeepWork
                    receipt output.1 first +
                  actualWholeSymmetricVelocityMultiplierGapTraceWork
                    receipt output.1 first)) -
              2 * actualWholeRowViscousPayment receipt output.1 := by
  rw [receiptHighFrequencyProjectedParabolicTrace_eq_complementPair_sub_viscous]
  have doubled :
      2 *
          (∑' output : NonzeroIntegerWavevector,
            if output.1 ∈ wholeRestartModes radius then 0
            else
              (∑' first : IntegerWavevector,
                  actualWholePairOccurrenceWork
                    receipt output.1 first) -
                actualWholeRowViscousPayment receipt output.1) =
        ∑' output : NonzeroIntegerWavevector,
          if output.1 ∈ wholeRestartModes radius then 0
          else
            (∑' first : IntegerWavevector,
                (actualWholeSymmetricVelocityReflectedKeepWork
                    receipt output.1 first +
                  actualWholeSymmetricVelocityMultiplierGapTraceWork
                    receipt output.1 first)) -
              2 * actualWholeRowViscousPayment receipt output.1 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro output
    by_cases outputMem : output.1 ∈ wholeRestartModes radius
    · simp [outputMem]
    · rw [if_neg outputMem, if_neg outputMem]
      have pairTwoEq :
          2 *
              (∑' first : IntegerWavevector,
                actualWholePairOccurrenceWork
                  receipt output.1 first) =
            ∑' first : IntegerWavevector,
              (actualWholeSymmetricVelocityReflectedKeepWork
                  receipt output.1 first +
                actualWholeSymmetricVelocityMultiplierGapTraceWork
                  receipt output.1 first) := by
        rw [←
          tsum_actualWholeSymmetricVelocityEnstrophyWork_eq_two_mul_pairOccurrenceWork
            receipt output.1 output.2]
        apply tsum_congr
        intro first
        exact
          actualWholeSymmetricVelocityEnstrophyWork_eq_reflectedKeep_add_multiplierGapTrace
            receipt output.1 first
      rw [← pairTwoEq]
      ring
  rw [← doubled]
  ring

/-- The outside projected trace can be read entirely on the original NS
receipt as reflected triad work, literal differences of viscous rates on the
same pair-and-swap incidence, and the output-row viscous debit.  In
particular the multiplier gap is not an autonomous high-frequency source. -/
theorem
    receiptHighFrequencyProjectedParabolicTrace_eq_literalTriadViscousRateBalance
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    receiptHighFrequencyProjectedParabolicTrace receipt radius =
      (1 / 2 : Real) *
        ∑' output : NonzeroIntegerWavevector,
          if output.1 ∈ wholeRestartModes radius then 0
          else
            (∑' first : IntegerWavevector,
                (nu.coeff *
                    actualWholeSymmetricVelocityReflectedKeepWork
                      receipt output.1 first +
                  ∫ time,
                    let second := output.1 - first
                    2 *
                      ((nu.coeff * integerWaveViscousMultiplier output.1 -
                            nu.coeff * integerWaveViscousMultiplier second) *
                          actualWholeVelocityBilinearEnergyOccurrence
                            receipt first second time +
                        (nu.coeff * integerWaveViscousMultiplier output.1 -
                            nu.coeff * integerWaveViscousMultiplier first) *
                          actualWholeVelocityBilinearEnergyOccurrence
                            receipt second first time)
                    ∂(commonTimeMeasure requestedTime))) -
              2 * nu.coeff *
                actualWholeRowViscousPayment receipt output.1 := by
  rw [
    receiptHighFrequencyProjectedParabolicTrace_eq_half_complementReflectedTransport_sub_viscous]
  rw [show nu.coeff / 2 = (1 / 2 : Real) * nu.coeff by ring,
    mul_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro output
  by_cases outputMem : output.1 ∈ wholeRestartModes radius
  · simp [outputMem]
  · rw [if_neg outputMem, if_neg outputMem, mul_sub, ← tsum_mul_left]
    congr 1
    · apply tsum_congr
      intro first
      rw [mul_add,
        viscosity_mul_actualWholeSymmetricVelocityMultiplierGapTraceWork_eq_integral_literalViscousRateDifference]
    · ring

/-- Before the input-pair quotient, the same receipt settles its projected
trace by the literal pair-incidence work, the tangent/viscous cross trace,
and the nonnegative viscous debit.  No pair, output, sign, or bound is chosen
by the caller. -/
theorem
    receiptHighFrequencyProjectedParabolicTrace_add_pairOccurrenceWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    receiptHighFrequencyProjectedParabolicTrace receipt radius +
        nu.coeff *
          actualWholeFinitePairOccurrenceWork
            receipt (wholeRestartModes radius) =
      2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt))) +
        nu.coeff *
          actualWholeFiniteViscousPayment
            receipt (wholeRestartModes radius) := by
  rw [actualWholeFinitePairOccurrenceWork_eq_preQuotientWork
    receipt (wholeRestartModes radius)
    (zero_not_mem_wholeRestartModes radius)]
  have preQuotientEq :
      actualWholeFinitePreQuotientWork
          receipt (wholeRestartModes radius) =
        actualWholeFiniteNonlinearWork
          receipt (wholeRestartModes radius) := by
    calc
      actualWholeFinitePreQuotientWork
          receipt (wholeRestartModes radius) =
          actualWholeFiniteBilinearWork
            receipt (wholeRestartModes radius) :=
        actualWholeFinitePreQuotientWork_eq_bilinearWork
          receipt (wholeRestartModes radius)
      _ = actualWholeFiniteNonlinearWork
          receipt (wholeRestartModes radius) :=
        (actualWholeFiniteNonlinearWork_eq_bilinearWork
          receipt (wholeRestartModes radius)).symm
  rw [preQuotientEq,
    ← actualWholeFiniteNetWork_add_viscousPayment]
  unfold receiptHighFrequencyProjectedParabolicTrace
  ring

/-- The projected parabolic traces telescope on every exact interval of the
original whole-restart run.  The cutoff and interval endpoints remain caller
coordinates; every summand is generated by that row's native whole-PDE
write. -/
theorem wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
    (initial : GeneratedWholeRestartCurrent nu)
    (radius start finish : Nat)
    (startLeFinish : start ≤ finish) :
    (∑ index ∈ Finset.Ico start finish,
      receiptHighFrequencyProjectedParabolicTrace
        (run initial index).nextContact.prefixReceipt radius) =
      nu.coeff *
        (restartPhysicalHighFrequencyTailMass initial finish radius -
          restartPhysicalHighFrequencyTailMass initial start radius) := by
  let tailMass : Nat → Real := fun index =>
    restartPhysicalHighFrequencyTailMass initial index radius
  have edgeTrace (index : Nat) :
      receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius =
        nu.coeff * (tailMass (index + 1) - tailMass index) := by
    rw [receiptHighFrequencyProjectedParabolicTrace_eq_boundaryComplement]
    rw [(run initial index).nextContact_prefix_terminal]
    rfl
  calc
    (∑ index ∈ Finset.Ico start finish,
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius) =
        ∑ index ∈ Finset.Ico start finish,
          nu.coeff * (tailMass (index + 1) - tailMass index) := by
      apply Finset.sum_congr rfl
      intro index _indexMem
      exact edgeTrace index
    _ = nu.coeff *
        ∑ index ∈ Finset.Ico start finish,
          (tailMass (index + 1) - tailMass index) := by
      rw [Finset.mul_sum]
    _ = nu.coeff *
        ((∑ index ∈ Finset.range finish,
            (tailMass (index + 1) - tailMass index)) -
          ∑ index ∈ Finset.range start,
            (tailMass (index + 1) - tailMass index)) := by
      rw [Finset.sum_Ico_eq_sub _ startLeFinish]
    _ = nu.coeff *
        ((tailMass finish - tailMass 0) -
          (tailMass start - tailMass 0)) := by
      rw [Finset.sum_range_sub, Finset.sum_range_sub]
    _ = nu.coeff * (tailMass finish - tailMass start) := by ring
    _ = nu.coeff *
        (restartPhysicalHighFrequencyTailMass initial finish radius -
          restartPhysicalHighFrequencyTailMass initial start radius) := by
      rfl

/-- Summing the receipt-level incidence equation preserves the exact same
`Ico`, cutoff, and native whole-PDE writes.  The pair table is still indexed
before its fixed-output quotient, and viscosity remains an explicit debit. -/
theorem
    wholeRestartIcoHighFrequencyProjectedParabolicTrace_add_pairOccurrenceWork
    (initial : GeneratedWholeRestartCurrent nu)
    (radius start finish : Nat) :
    (∑ index ∈ Finset.Ico start finish,
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius) +
        nu.coeff *
          (∑ index ∈ Finset.Ico start finish,
            actualWholeFinitePairOccurrenceWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes radius)) =
      (∑ index ∈ Finset.Ico start finish,
        2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (run initial index).nextContact.prefixReceipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt)))) +
        nu.coeff *
          (∑ index ∈ Finset.Ico start finish,
            actualWholeFiniteViscousPayment
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes radius)) := by
  calc
    (∑ index ∈ Finset.Ico start finish,
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius) +
        nu.coeff *
          (∑ index ∈ Finset.Ico start finish,
            actualWholeFinitePairOccurrenceWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes radius)) =
      ∑ index ∈ Finset.Ico start finish,
        (receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt radius +
          nu.coeff *
            actualWholeFinitePairOccurrenceWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes radius)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ index ∈ Finset.Ico start finish,
        (2 * RCLike.re (inner ℂ
            (puncturedEuclideanSpaceTimeState
              (run initial index).nextContact.prefixReceipt.wholeTangent)
            (puncturedEuclideanSpaceTimeState
              (receiptViscousNegativeOneState
                (run initial index).nextContact.prefixReceipt))) +
          nu.coeff *
            actualWholeFiniteViscousPayment
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes radius)) := by
        apply Finset.sum_congr rfl
        intro index _indexMem
        exact
          receiptHighFrequencyProjectedParabolicTrace_add_pairOccurrenceWork
            (run initial index).nextContact.prefixReceipt radius
    _ =
      (∑ index ∈ Finset.Ico start finish,
        2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (run initial index).nextContact.prefixReceipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt)))) +
        nu.coeff *
          (∑ index ∈ Finset.Ico start finish,
            actualWholeFiniteViscousPayment
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes radius)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Source-native cofinal block effect -/

private theorem
    actualWholeFinitePairOccurrenceWork_ne_zero_generates_pairOccurrenceWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (workNonzero :
      actualWholeFinitePairOccurrenceWork receipt modes ≠ 0) :
    ∃ output ∈ modes,
      ∃ first : IntegerWavevector,
        actualWholePairOccurrenceWork receipt output first ≠ 0 := by
  unfold actualWholeFinitePairOccurrenceWork at workNonzero
  obtain ⟨output, outputMem, rowNonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero workNonzero
  refine ⟨output, outputMem, ?_⟩
  by_contra everyOccurrenceZero
  push Not at everyOccurrenceZero
  apply rowNonzero
  simp only [everyOccurrenceZero, tsum_zero]

/-- A bounded elapsed fibre only instantiates this source-native law.  The
original whole-restart receipts select a strictly increasing family of exact
`Ico` blocks; every block writes positive omitted-vorticity trace, its full
pair/cross/viscous balance, and one literal nonzero PDE channel. -/
theorem
    elapsedBounded_generatesCofinalHighFrequencyProjectedParabolicTrace
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ contactIndex : Nat → Nat,
      contactIndex 0 = 0 ∧
        StrictMono contactIndex ∧
        ∀ step : Nat,
          let radius := 2 * (contactIndex step + 1)
          let interval :=
            Finset.Ico (contactIndex step) (contactIndex (step + 1))
          let trace :=
            ∑ index ∈ interval,
              receiptHighFrequencyProjectedParabolicTrace
                (run initial index).nextContact.prefixReceipt radius
          let pairWork :=
            ∑ index ∈ interval,
              actualWholeFinitePairOccurrenceWork
                (run initial index).nextContact.prefixReceipt
                (wholeRestartModes radius)
          let tangentViscousCross :=
            ∑ index ∈ interval,
              2 * RCLike.re (inner ℂ
                (puncturedEuclideanSpaceTimeState
                  (run initial index).nextContact.prefixReceipt.wholeTangent)
                (puncturedEuclideanSpaceTimeState
                  (receiptViscousNegativeOneState
                    (run initial index).nextContact.prefixReceipt)))
          let viscousDebit :=
            ∑ index ∈ interval,
              actualWholeFiniteViscousPayment
                (run initial index).nextContact.prefixReceipt
                (wholeRestartModes radius)
          nu.coeff < trace ∧
            trace + nu.coeff * pairWork =
              tangentViscousCross + nu.coeff * viscousDebit ∧
            ∃ index ∈ interval,
              receiptHighFrequencyProjectedParabolicTrace
                  (run initial index).nextContact.prefixReceipt radius ≠ 0 ∧
                ((∃ output ∈ wholeRestartModes radius,
                    ∃ first : IntegerWavevector,
                      actualWholePairOccurrenceWork
                        (run initial index).nextContact.prefixReceipt
                        output first ≠ 0) ∨
                  2 * RCLike.re (inner ℂ
                      (puncturedEuclideanSpaceTimeState
                        (run initial index).nextContact.prefixReceipt.wholeTangent)
                      (puncturedEuclideanSpaceTimeState
                        (receiptViscousNegativeOneState
                          (run initial index).nextContact.prefixReceipt))) ≠ 0 ∨
                  actualWholeFiniteViscousPayment
                      (run initial index).nextContact.prefixReceipt
                      (wholeRestartModes radius) ≠ 0) := by
  have existsLater (cursor : Nat) :
      ∃ later : Nat,
        cursor < later ∧
          restartPhysicalHighFrequencyTailMass
                initial cursor (2 * (cursor + 1)) + 1 <
            restartPhysicalHighFrequencyTailMass
              initial later (2 * (cursor + 1)) := by
    let currentMass :=
      restartPhysicalHighFrequencyTailMass
        initial cursor (2 * (cursor + 1))
    let requested := currentMass + 2
    have eventuallyLarge :
        ∀ᶠ index : Nat in atTop,
          requested ≤
            restartPhysicalHighFrequencyTailMass
              initial index (2 * (cursor + 1)) :=
      tendsto_atTop.1
        (tendsto_restartPhysicalHighFrequencyTailMass_atTop_of_elapsedTime_bddAbove
          initial elapsedBounded (2 * (cursor + 1)))
        requested
    obtain ⟨threshold, thresholdSpec⟩ :=
      eventually_atTop.1 eventuallyLarge
    let later := max (cursor + 1) threshold
    refine ⟨later, ?_, ?_⟩
    · exact
        (Nat.lt_succ_self cursor).trans_le
          (Nat.le_max_left _ _)
    · have largeAtLater :=
        thresholdSpec later (Nat.le_max_right _ _)
      dsimp only [requested, currentMass] at largeAtLater ⊢
      linarith
  let nextIndex : Nat → Nat := fun cursor =>
    Nat.find (existsLater cursor)
  have nextIndex_spec (cursor : Nat) :
      cursor < nextIndex cursor ∧
        restartPhysicalHighFrequencyTailMass
              initial cursor (2 * (cursor + 1)) + 1 <
          restartPhysicalHighFrequencyTailMass
            initial (nextIndex cursor) (2 * (cursor + 1)) := by
    simpa only [nextIndex] using Nat.find_spec (existsLater cursor)
  let contactIndex : Nat → Nat := fun step =>
    Nat.rec 0 (fun _ cursor => nextIndex cursor) step
  have contactIndex_zero : contactIndex 0 = 0 := by
    rfl
  have contactIndex_succ (step : Nat) :
      contactIndex (step + 1) = nextIndex (contactIndex step) := by
    simp only [contactIndex]
  have contactIndex_lt_succ (step : Nat) :
      contactIndex step < contactIndex (step + 1) := by
    rw [contactIndex_succ]
    exact (nextIndex_spec (contactIndex step)).1
  have contactIndex_strictMono : StrictMono contactIndex := by
    apply strictMono_nat_of_lt_succ
    exact contactIndex_lt_succ
  refine
    ⟨contactIndex, contactIndex_zero, contactIndex_strictMono, ?_⟩
  intro step
  have tracePositive :
      nu.coeff <
        ∑ index ∈
            Finset.Ico (contactIndex step) (contactIndex (step + 1)),
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt
            (2 * (contactIndex step + 1)) := by
    have tailGap :
        restartPhysicalHighFrequencyTailMass
              initial (contactIndex step)
                (2 * (contactIndex step + 1)) + 1 <
          restartPhysicalHighFrequencyTailMass
            initial (contactIndex (step + 1))
              (2 * (contactIndex step + 1)) := by
      rw [contactIndex_succ]
      exact (nextIndex_spec (contactIndex step)).2
    rw [wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
      initial (2 * (contactIndex step + 1))
      (contactIndex step) (contactIndex (step + 1))
      (contactIndex_lt_succ step).le]
    nlinarith [nu.coeff_pos]
  have blockBalance :=
    wholeRestartIcoHighFrequencyProjectedParabolicTrace_add_pairOccurrenceWork
      initial (2 * (contactIndex step + 1))
      (contactIndex step) (contactIndex (step + 1))
  refine ⟨tracePositive, blockBalance, ?_⟩
  have traceSumNonzero :
      (∑ index ∈
          Finset.Ico (contactIndex step) (contactIndex (step + 1)),
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt
          (2 * (contactIndex step + 1))) ≠ 0 :=
    ne_of_gt (nu.coeff_pos.trans tracePositive)
  obtain ⟨index, indexMem, receiptTraceNonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero traceSumNonzero
  refine ⟨index, indexMem, receiptTraceNonzero, ?_⟩
  let receipt := (run initial index).nextContact.prefixReceipt
  let radius := 2 * (contactIndex step + 1)
  by_cases pairNonzero :
      actualWholeFinitePairOccurrenceWork
          receipt (wholeRestartModes radius) ≠ 0
  · exact Or.inl
      (actualWholeFinitePairOccurrenceWork_ne_zero_generates_pairOccurrenceWork
        receipt (wholeRestartModes radius) pairNonzero)
  by_cases crossNonzero :
      2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt))) ≠ 0
  · exact Or.inr (Or.inl crossNonzero)
  refine Or.inr (Or.inr ?_)
  intro viscousZero
  apply receiptTraceNonzero
  have receiptBalance :=
    receiptHighFrequencyProjectedParabolicTrace_add_pairOccurrenceWork
      receipt radius
  have pairZero := not_ne_iff.mp pairNonzero
  have crossZero := not_ne_iff.mp crossNonzero
  dsimp only [receipt, radius] at receiptBalance pairZero crossZero viscousZero ⊢
  rw [pairZero, crossZero, viscousZero] at receiptBalance
  simpa using receiptBalance

end FullFrameBoundaryVorticityNativeHighFrequencyProjectedParabolicTrace
end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
