import H0mework.NavierStokes.PairRestart.PairDuhamelKineticTriadRedirect
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation

/-!
# Same-receipt symmetric velocity multiplier-gap transport

This module compiles one actual whole-restart pair receipt from its complete
swap orbit on the vorticity carrier to the Laplacian-weighted velocity
carrier.  It then transports that action through the source-owned reflected
triad relation, retaining the reflected keep and the forced multiplier-gap
trace as one paired occurrence.

The finite-output theorem keeps the two transported summands inside the same
input-lattice tsum.  No separate summability law, cofinal relation, cutoff
orientation, target state, or settlement is supplied by the caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSymmetricVelocityMultiplierGapTransport

open scoped BigOperators

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect

noncomputable section

variable {nu : Viscosity}

/-! ## Occurrencewise Hodge compiler on a complete swap orbit -/

/-- Laplacian-weighted velocity-pair power on the complete swap orbit of one
actual vorticity occurrence. -/
def actualWholeSymmetricVelocityEnstrophyPower
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : Real :=
  2 * integerWaveViscousMultiplier output *
    (actualWholeVelocityBilinearEnergyOccurrence
        receipt first (output - first) time +
      actualWholeVelocityBilinearEnergyOccurrence
        receipt (output - first) first time)

/-- Pair-plus-swap on the vorticity carrier is exactly the weighted symmetric
velocity action on the same receipt and the same physical time. -/
theorem actualWholeContinuousPairPower_add_swap_eq_symmetricVelocityEnstrophyPower
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (time : Icc (0 : Real) requestedTime) :
    actualWholeContinuousPairPower receipt output first time +
        actualWholeContinuousPairPower
          receipt output (output - first) time =
      actualWholeSymmetricVelocityEnstrophyPower
        receipt output first time := by
  let second : IntegerWavevector := output - first
  let state : ComplexVorticityHilbertState := receipt.wholePath time
  let velocityPair : ComplexCoordinateVector :=
    actualWholeContinuousVelocityPairVector receipt first second time +
      actualWholeContinuousVelocityPairVector receipt second first time
  have outputEq : first + second = output := by
    simp [second]
  have curlEq :
      fourierCurlCoefficient output velocityPair =
        actualWholeContinuousPairVector receipt output first time +
          actualWholeContinuousPairVector receipt output second time := by
    dsimp only [velocityPair]
    rw [← outputEq]
    exact
      actualWholeContinuousVelocityPair_add_swap_curl_eq_pairVector
        receipt first second time
  have hodge :=
    complexCoordinateRealInner_biotSavartVelocityCoefficient
      output outputNonzero (state output)
      (fourierCurlCoefficient output velocityPair)
      (wholePath_transverse receipt time output)
  rw [biotSavartVelocityCoefficient_fourierCurlCoefficient
      output velocityPair outputNonzero] at hodge
  rw [complexCoordinateRealInner_transverseProjection
      output
      (biotSavartVelocityCoefficient output (state output))
      velocityPair outputNonzero
      (complexWavevector_dot_biotSavartVelocityCoefficient
        output (state output))] at hodge
  have multiplierNonzero :
      integerWaveViscousMultiplier output ≠ 0 :=
    ne_of_gt (integerWaveViscousMultiplier_pos
      (⟨output, outputNonzero⟩ : NonzeroIntegerWavevector))
  have pairingEq :
      complexCoordinateRealInner
          (state output) (fourierCurlCoefficient output velocityPair) =
        integerWaveViscousMultiplier output *
          complexCoordinateRealInner
            (finiteStateVelocityCoefficient state output) velocityPair := by
    have multiplied := (eq_div_iff multiplierNonzero).mp hodge
    calc
      complexCoordinateRealInner
          (state output) (fourierCurlCoefficient output velocityPair) =
          complexCoordinateRealInner
              (biotSavartVelocityCoefficient output (state output))
              velocityPair *
            integerWaveViscousMultiplier output := multiplied.symm
      _ = integerWaveViscousMultiplier output *
          complexCoordinateRealInner
            (finiteStateVelocityCoefficient state output) velocityPair := by
        rw [mul_comm]
        rfl
  calc
    actualWholeContinuousPairPower receipt output first time +
          actualWholeContinuousPairPower
            receipt output (output - first) time =
        2 * complexCoordinateRealInner
          (state output)
          (actualWholeContinuousPairVector receipt output first time +
            actualWholeContinuousPairVector receipt output second time) := by
      unfold actualWholeContinuousPairPower
        actualWholeContinuousPairVector
      rw [complexCoordinateRealInner_add_right]
      simp only [state, second]
      ring
    _ = 2 * complexCoordinateRealInner
          (state output) (fourierCurlCoefficient output velocityPair) := by
      rw [curlEq]
    _ = 2 * integerWaveViscousMultiplier output *
          complexCoordinateRealInner
            (finiteStateVelocityCoefficient state output) velocityPair := by
      rw [pairingEq]
      ring
    _ = actualWholeSymmetricVelocityEnstrophyPower
          receipt output first time := by
      dsimp only [velocityPair]
      unfold actualWholeSymmetricVelocityEnstrophyPower
        actualWholeContinuousVelocityPairVector
        actualWholeVelocityBilinearEnergyOccurrence
        finiteStateVelocityBilinearEnergyOccurrence
      rw [complexCoordinateRealInner_add_right]
      simp only [state, second, outputEq, add_comm]

/-! ## Time-integrated swap-orbit work -/

private theorem actualWholeContinuousPairPower_integrable
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    Integrable
      (actualWholeContinuousPairPower receipt output first)
      (commonTimeMeasure requestedTime) := by
  have originalIntegrable :
      Integrable
        (actualWholePairPower receipt output first)
        (commonTimeMeasure requestedTime) := by
    apply Integrable.mono'
      (actualWholePairPowerMass_integrable receipt output)
      (actualWholePairPower_aestronglyMeasurable
        receipt output first)
    filter_upwards with time
    exact
      (summable_norm_actualWholePairPower receipt output time).le_tsum
        first (fun _ _ => norm_nonneg _)
  exact originalIntegrable.congr
    (actualWholeContinuousPairPower_ae_eq receipt output first).symm

/-- Physical-time integral of the symmetric weighted velocity action. -/
def actualWholeSymmetricVelocityEnstrophyWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) : Real :=
  ∫ time,
    actualWholeSymmetricVelocityEnstrophyPower
      receipt output first time
    ∂(commonTimeMeasure requestedTime)

/-- Time integration preserves the exact pair-plus-swap Hodge compiler. -/
theorem actualWholePairOccurrenceWork_add_swap_eq_symmetricVelocityEnstrophyWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    actualWholePairOccurrenceWork receipt output first +
        actualWholePairOccurrenceWork receipt output (output - first) =
      actualWholeSymmetricVelocityEnstrophyWork
        receipt output first := by
  rw [← integral_actualWholeContinuousPairPower_eq_occurrenceWork
      receipt output first,
    ← integral_actualWholeContinuousPairPower_eq_occurrenceWork
      receipt output (output - first),
    ← integral_add
      (actualWholeContinuousPairPower_integrable receipt output first)
      (actualWholeContinuousPairPower_integrable
        receipt output (output - first))]
  unfold actualWholeSymmetricVelocityEnstrophyWork
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun time =>
    actualWholeContinuousPairPower_add_swap_eq_symmetricVelocityEnstrophyPower
      receipt output first outputNonzero time

/-- Summing over the complete input lattice preserves both members of every
swap orbit.  The factor two is exact and no orientation is selected. -/
theorem tsum_actualWholeSymmetricVelocityEnstrophyWork_eq_two_mul_pairOccurrenceWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    (∑' first : IntegerWavevector,
        actualWholeSymmetricVelocityEnstrophyWork
          receipt output first) =
      2 * ∑' first : IntegerWavevector,
        actualWholePairOccurrenceWork receipt output first := by
  have directSummable :
      Summable fun first : IntegerWavevector =>
        actualWholePairOccurrenceWork receipt output first :=
    (hasSum_actualWholePairOccurrenceWork receipt output).summable
  have swappedSummable :
      Summable fun first : IntegerWavevector =>
        actualWholePairOccurrenceWork receipt output (output - first) := by
    exact ((outputSubEquiv output).summable_iff).2 directSummable
  have swappedTsum :
      (∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork receipt output (output - first)) =
        ∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork receipt output first := by
    exact (outputSubEquiv output).tsum_eq
      (actualWholePairOccurrenceWork receipt output)
  calc
    (∑' first : IntegerWavevector,
        actualWholeSymmetricVelocityEnstrophyWork
          receipt output first) =
        ∑' first : IntegerWavevector,
          (actualWholePairOccurrenceWork receipt output first +
            actualWholePairOccurrenceWork
              receipt output (output - first)) := by
      apply tsum_congr
      intro first
      exact
        (actualWholePairOccurrenceWork_add_swap_eq_symmetricVelocityEnstrophyWork
          receipt output first outputNonzero).symm
    _ =
        (∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork receipt output first) +
        ∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork
            receipt output (output - first) := by
      rw [Summable.tsum_add directSummable swappedSummable]
    _ = 2 * ∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork receipt output first := by
      rw [swappedTsum]
      ring

/-! ## Same-receipt reflected keep and multiplier-gap trace -/

/-- The native reflected-triad part of the symmetric weighted occurrence.

The reflection is performed before the fixed-output quotient.  Its two
outputs are the negatives of the complementary input and the first input, so
this is a whole-lattice relation term rather than an endomorphism of the
current finite output inventory. -/
def actualWholeSymmetricVelocityReflectedKeepPower
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : Real :=
  let second := output - first
  2 *
    (-integerWaveViscousMultiplier second *
        actualWholeVelocityBilinearEnergyOccurrence
          receipt first (outputNegSecondEquiv first second) time -
      integerWaveViscousMultiplier first *
        actualWholeVelocityBilinearEnergyOccurrence
          receipt second (outputNegSecondEquiv second first) time)

/-- The trace forced by transporting the reflected-triad relation through
the output-dependent Laplacian multiplier.  Every coefficient is determined
by the same actual output and its two actual inputs. -/
def actualWholeSymmetricVelocityMultiplierGapTracePower
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : Real :=
  let second := output - first
  2 *
    ((integerWaveViscousMultiplier output -
          integerWaveViscousMultiplier second) *
        actualWholeVelocityBilinearEnergyOccurrence
          receipt first second time +
      (integerWaveViscousMultiplier output -
          integerWaveViscousMultiplier first) *
        actualWholeVelocityBilinearEnergyOccurrence
          receipt second first time)

/-- Multiplying the forced gap by the receipt viscosity exposes the literal
differences of viscous rates on the same pair-and-swap triad.  The gap is
therefore not an autonomous high-frequency channel. -/
theorem
    viscosity_mul_actualWholeSymmetricVelocityMultiplierGapTracePower_eq_literalViscousRateDifference
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    nu.coeff *
        actualWholeSymmetricVelocityMultiplierGapTracePower
          receipt output first time =
      2 *
        ((nu.coeff * integerWaveViscousMultiplier output -
              nu.coeff * integerWaveViscousMultiplier (output - first)) *
            actualWholeVelocityBilinearEnergyOccurrence
              receipt first (output - first) time +
          (nu.coeff * integerWaveViscousMultiplier output -
              nu.coeff * integerWaveViscousMultiplier first) *
            actualWholeVelocityBilinearEnergyOccurrence
              receipt (output - first) first time) := by
  unfold actualWholeSymmetricVelocityMultiplierGapTracePower
  dsimp only
  ring

/-- Residual transport on one complete swap orbit: the actual weighted
velocity action is exactly its native reflected keep plus the uniquely
forced multiplier-gap trace.  No output orientation or cancellation
certificate is chosen by the caller. -/
theorem
    actualWholeSymmetricVelocityEnstrophyPower_ae_eq_reflectedKeep_add_multiplierGapTrace
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualWholeSymmetricVelocityEnstrophyPower
          receipt output first time =
        actualWholeSymmetricVelocityReflectedKeepPower
            receipt output first time +
          actualWholeSymmetricVelocityMultiplierGapTracePower
            receipt output first time := by
  let second : IntegerWavevector := output - first
  have firstReflect :=
    actualWholeVelocityBilinearEnergyOccurrence_reflect_ae
      receipt first second
  have secondReflect :=
    actualWholeVelocityBilinearEnergyOccurrence_reflect_ae
      receipt second first
  filter_upwards [firstReflect, secondReflect] with
      time firstReflectEq secondReflectEq
  unfold actualWholeSymmetricVelocityEnstrophyPower
    actualWholeSymmetricVelocityReflectedKeepPower
    actualWholeSymmetricVelocityMultiplierGapTracePower
  dsimp only [second]
  rw [firstReflectEq, secondReflectEq]
  ring

/-- Physical-time work retained by the native reflected relation. -/
def actualWholeSymmetricVelocityReflectedKeepWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) : Real :=
  ∫ time,
    actualWholeSymmetricVelocityReflectedKeepPower
      receipt output first time
    ∂(commonTimeMeasure requestedTime)

/-- Physical-time work of the forced multiplier-gap trace. -/
def actualWholeSymmetricVelocityMultiplierGapTraceWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) : Real :=
  ∫ time,
    actualWholeSymmetricVelocityMultiplierGapTracePower
      receipt output first time
    ∂(commonTimeMeasure requestedTime)

/-- Physical-time integration preserves the same literal viscous-rate
incidence without adding a norm, sign, or summability premise. -/
theorem
    viscosity_mul_actualWholeSymmetricVelocityMultiplierGapTraceWork_eq_integral_literalViscousRateDifference
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    nu.coeff *
        actualWholeSymmetricVelocityMultiplierGapTraceWork
          receipt output first =
      ∫ time,
        let second := output - first
        2 *
          ((nu.coeff * integerWaveViscousMultiplier output -
                nu.coeff * integerWaveViscousMultiplier second) *
              actualWholeVelocityBilinearEnergyOccurrence
                receipt first second time +
            (nu.coeff * integerWaveViscousMultiplier output -
                nu.coeff * integerWaveViscousMultiplier first) *
              actualWholeVelocityBilinearEnergyOccurrence
                receipt second first time)
        ∂(commonTimeMeasure requestedTime) := by
  unfold actualWholeSymmetricVelocityMultiplierGapTraceWork
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun time =>
    viscosity_mul_actualWholeSymmetricVelocityMultiplierGapTracePower_eq_literalViscousRateDifference
      receipt output first time

private theorem actualWholeSymmetricVelocityReflectedKeepPower_integrable
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    Integrable
      (actualWholeSymmetricVelocityReflectedKeepPower
        receipt output first)
      (commonTimeMeasure requestedTime) := by
  let second : IntegerWavevector := output - first
  have firstContinuous :=
    actualWholeVelocityBilinearEnergyOccurrence_continuous
      receipt first (outputNegSecondEquiv first second)
  have secondContinuous :=
    actualWholeVelocityBilinearEnergyOccurrence_continuous
      receipt second (outputNegSecondEquiv second first)
  apply Continuous.integrable_of_hasCompactSupport
    (f := actualWholeSymmetricVelocityReflectedKeepPower
      receipt output first)
  · unfold actualWholeSymmetricVelocityReflectedKeepPower
    dsimp only [second]
    exact continuous_const.mul
      ((continuous_const.mul firstContinuous).sub
        (continuous_const.mul secondContinuous))
  · exact HasCompactSupport.of_compactSpace _

private theorem actualWholeSymmetricVelocityMultiplierGapTracePower_integrable
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    Integrable
      (actualWholeSymmetricVelocityMultiplierGapTracePower
        receipt output first)
      (commonTimeMeasure requestedTime) := by
  let second : IntegerWavevector := output - first
  have firstContinuous :=
    actualWholeVelocityBilinearEnergyOccurrence_continuous
      receipt first second
  have secondContinuous :=
    actualWholeVelocityBilinearEnergyOccurrence_continuous
      receipt second first
  apply Continuous.integrable_of_hasCompactSupport
    (f := actualWholeSymmetricVelocityMultiplierGapTracePower
      receipt output first)
  · unfold actualWholeSymmetricVelocityMultiplierGapTracePower
    dsimp only [second]
    exact continuous_const.mul
      ((continuous_const.mul firstContinuous).add
        (continuous_const.mul secondContinuous))
  · exact HasCompactSupport.of_compactSpace _

/-- Time integration preserves the exact residual transport law on the same
actual swap-orbit receipt. -/
theorem
    actualWholeSymmetricVelocityEnstrophyWork_eq_reflectedKeep_add_multiplierGapTrace
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    actualWholeSymmetricVelocityEnstrophyWork
        receipt output first =
      actualWholeSymmetricVelocityReflectedKeepWork
          receipt output first +
        actualWholeSymmetricVelocityMultiplierGapTraceWork
          receipt output first := by
  unfold actualWholeSymmetricVelocityEnstrophyWork
    actualWholeSymmetricVelocityReflectedKeepWork
    actualWholeSymmetricVelocityMultiplierGapTraceWork
  rw [← integral_add
    (actualWholeSymmetricVelocityReflectedKeepPower_integrable
      receipt output first)
    (actualWholeSymmetricVelocityMultiplierGapTracePower_integrable
      receipt output first)]
  apply integral_congr_ae
  exact
    actualWholeSymmetricVelocityEnstrophyPower_ae_eq_reflectedKeep_add_multiplierGapTrace
      receipt output first

/-- Finite output aggregation of the same exact paired residual transport on
any zero-free inventory.  The reflected keep and multiplier-gap trace remain
inside one input tsum. -/
theorem
    actualWholeFinitePairOccurrenceWork_two_mul_eq_reflectedTransport_of_zero_not_mem
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) :
    2 * actualWholeFinitePairOccurrenceWork
          receipt modes =
      ∑ output ∈ modes,
        ∑' first : IntegerWavevector,
          (actualWholeSymmetricVelocityReflectedKeepWork
              receipt output first +
            actualWholeSymmetricVelocityMultiplierGapTraceWork
              receipt output first) := by
  unfold actualWholeFinitePairOccurrenceWork
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output outputMem
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    exact zeroNotMem outputMem
  rw [←
    tsum_actualWholeSymmetricVelocityEnstrophyWork_eq_two_mul_pairOccurrenceWork
      receipt output outputNonzero]
  apply tsum_congr
  intro first
  exact
    actualWholeSymmetricVelocityEnstrophyWork_eq_reflectedKeep_add_multiplierGapTrace
      receipt output first

/-- On any zero-free finite output inventory, the paired reflected transport
minus its literal viscous payment is exactly twice the same receipt's
coefficient-enstrophy change. -/
theorem
    actualWholeFiniteReflectedTransport_sub_two_mul_viscous_eq_two_mul_endpointChange_of_zero_not_mem
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) :
    (∑ output ∈ modes,
        ∑' first : IntegerWavevector,
          (actualWholeSymmetricVelocityReflectedKeepWork
              receipt output first +
            actualWholeSymmetricVelocityMultiplierGapTraceWork
              receipt output first)) -
        2 * actualWholeFiniteViscousPayment receipt modes =
      2 * (finiteStateVorticityCoefficientEnstrophy modes
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            finiteStateVorticityCoefficientEnstrophy modes initialState) := by
  have transport :=
    actualWholeFinitePairOccurrenceWork_two_mul_eq_reflectedTransport_of_zero_not_mem
      receipt modes zeroNotMem
  have balance :=
    actualWholeFinitePairOccurrenceWork_eq_terminal_sub_initial_add_viscousPayment
      receipt modes zeroNotMem
  linarith

/-- For one fixed zero-free inventory, the paired reflected transport minus
the literal viscous payment telescopes through every actual receipt in a
chronological half-open restart block. -/
theorem
    wholeRestartIcoFiniteReflectedTransport_sub_two_mul_viscous_telescope
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (start finish : Nat)
    (startLeFinish : start ≤ finish) :
    (∑ index ∈ Finset.Ico start finish,
      ((∑ output ∈ modes,
          ∑' first : IntegerWavevector,
            (actualWholeSymmetricVelocityReflectedKeepWork
                (run initial index).nextContact.prefixReceipt output first +
              actualWholeSymmetricVelocityMultiplierGapTraceWork
                (run initial index).nextContact.prefixReceipt output first)) -
        2 * actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt modes)) =
      2 * (finiteStateVorticityCoefficientEnstrophy modes
              (run initial finish).contact.physicalState -
            finiteStateVorticityCoefficientEnstrophy modes
              (run initial start).contact.physicalState) := by
  let mass : Nat → Real := fun index =>
    finiteStateVorticityCoefficientEnstrophy modes
      (run initial index).contact.physicalState
  have edgeEq (index : Nat) :
      ((∑ output ∈ modes,
          ∑' first : IntegerWavevector,
            (actualWholeSymmetricVelocityReflectedKeepWork
                (run initial index).nextContact.prefixReceipt output first +
              actualWholeSymmetricVelocityMultiplierGapTraceWork
                (run initial index).nextContact.prefixReceipt output first)) -
        2 * actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt modes) =
        2 * (mass (index + 1) - mass index) := by
    have edge :=
      actualWholeFiniteReflectedTransport_sub_two_mul_viscous_eq_two_mul_endpointChange_of_zero_not_mem
        (run initial index).nextContact.prefixReceipt modes zeroNotMem
    rw [(run initial index).nextContact_prefix_terminal] at edge
    have nextContactEq :
        (run initial index).next.contact.physicalState =
          (run initial index).nextContact.physicalState := by
      rfl
    dsimp only [mass] at ⊢
    rw [run_succ, nextContactEq]
    exact edge
  simp_rw [edgeEq]
  rw [← Finset.mul_sum]
  rw [Finset.sum_Ico_eq_sub _ startLeFinish,
    Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- Canonical whole-restart inventory instance of the exact finite reflected
transport. -/
theorem actualWholeFinitePairOccurrenceWork_two_mul_eq_reflectedTransport
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    2 * actualWholeFinitePairOccurrenceWork
          receipt (wholeRestartModes radius) =
      ∑ output ∈ wholeRestartModes radius,
        ∑' first : IntegerWavevector,
          (actualWholeSymmetricVelocityReflectedKeepWork
              receipt output first +
            actualWholeSymmetricVelocityMultiplierGapTraceWork
              receipt output first) := by
  exact
    actualWholeFinitePairOccurrenceWork_two_mul_eq_reflectedTransport_of_zero_not_mem
      receipt (wholeRestartModes radius)
        (zero_not_mem_wholeRestartModes radius)

/-- The reflected keep and multiplier-gap trace are not a fourth physical
channel.  On the identical receipt and finite output inventory they are
settled by the whole-PDE enstrophy write: endpoint change plus the literal
viscous debit. -/
theorem
    actualWholeFiniteReflectedTransport_eq_two_mul_endpointChange_add_viscous
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    (∑ output ∈ wholeRestartModes radius,
        ∑' first : IntegerWavevector,
          (actualWholeSymmetricVelocityReflectedKeepWork
              receipt output first +
            actualWholeSymmetricVelocityMultiplierGapTraceWork
              receipt output first)) =
      2 * (finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes radius)
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes radius) initialState +
            actualWholeFiniteViscousPayment
              receipt (wholeRestartModes radius)) := by
  have settlement :=
    actualWholeFiniteReflectedTransport_sub_two_mul_viscous_eq_two_mul_endpointChange_of_zero_not_mem
      receipt (wholeRestartModes radius)
        (zero_not_mem_wholeRestartModes radius)
  linarith

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSymmetricVelocityMultiplierGapTransport
end NavierStokes
end SaturationMonoid
