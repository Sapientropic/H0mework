import H0mework.NavierStokes.Restart.EnstrophyWork
import H0mework.NavierStokes.ShellSources.WholeEnstrophyIdentity

/-!
# Pre-quotient nonlinear work on the native whole restart chain

The restart ledger already proves that finite accumulated physical time
forces unbounded actual nonlinear work.  This module identifies that restored
work with the literal whole-lattice bilinear Fourier coefficient before its
fixed-output pair series is aggregated.

The path, tangent, nonlinear row, viscosity, interval and endpoint all belong
to one `WholeContinuousMildSerrinReceipt`.  No occurrence norm, cutoff,
target pair or continuation certificate is introduced.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork

open scoped BigOperators Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork

noncomputable section

/-! ## Same-event interval identity -/

/-- Literal whole nonlinear work of one actual receipt row.  The whole
bilinear coefficient remains an absolutely summable fixed-output pair series
inside this definition; no coefficient or occurrence quotient has yet been
taken. -/
def actualWholeRowBilinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  if waveZero : wave = 0 then
    0
  else
    ∫ actual in (0 : ℝ)..requestedTime,
      2 * complexCoordinateRealInner
        (receipt.rowExtension wave waveZero actual)
        (commonTimeZeroExtension requestedTime
          (fun time =>
            wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 wave)
          actual)

private theorem actualWholeRowNetPower_intervalIntegrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    IntervalIntegrable
      (fun actual =>
        2 * complexCoordinateRealInner
          (receipt.rowExtension wave waveNonzero actual)
          (commonTimeZeroExtension requestedTime
            (receipt.rowTangent wave waveNonzero) actual))
      volume 0 requestedTime := by
  have pathAC :=
    receipt.rowExtension_absolutelyContinuous wave waveNonzero
  have energyAC :
      AbsolutelyContinuousOnInterval
        (fun actual =>
          complexCoordinateAmplitudeSq
            (receipt.rowExtension wave waveNonzero actual))
        0 requestedTime :=
    AbsolutelyContinuousOnInterval.comp_complexCoordinateAmplitudeSq
      pathAC
  apply energyAC.intervalIntegrable_deriv.congr_ae
  filter_upwards [
    ae_restrict_mem measurableSet_uIoc,
    ae_mono Measure.restrict_le_self
      (receipt.rowExtension_ae_hasDerivAt wave waveNonzero)] with
      actual actualMem derivative
  have actualDerivative :=
    complexCoordinateAmplitudeSq_hasDerivAt
      (receipt.rowExtension wave waveNonzero)
      actual
      (commonTimeZeroExtension requestedTime
        (receipt.rowTangent wave waveNonzero) actual)
      (derivative (uIoc_subset_uIcc actualMem))
  exact actualDerivative.deriv

private theorem actualWholeRowViscousPower_intervalIntegrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    IntervalIntegrable
      (fun actual =>
        2 * complexCoordinateRealInner
          (receipt.rowExtension wave waveNonzero actual)
          ((ν.coeff * integerWaveViscousMultiplier wave) •
            receipt.rowExtension wave waveNonzero actual))
      volume 0 requestedTime := by
  have pathContinuous :
      ContinuousOn
        (receipt.rowExtension wave waveNonzero)
        [[(0 : ℝ), requestedTime]] :=
    (receipt.rowExtension_absolutelyContinuous
      wave waveNonzero).continuousOn
  have pathContinuousIcc :
      ContinuousOn
        (receipt.rowExtension wave waveNonzero)
        (Icc (0 : ℝ) requestedTime) := by
    simpa only [uIcc_of_le receipt.requestedTimePos.le] using
      pathContinuous
  have viscousIntegrable :
      IntervalIntegrable
        (fun actual =>
          (ν.coeff * integerWaveViscousMultiplier wave) •
            receipt.rowExtension wave waveNonzero actual)
        volume 0 requestedTime :=
    (pathContinuousIcc.const_smul
      (ν.coeff * integerWaveViscousMultiplier wave))
        |>.intervalIntegrable_of_Icc receipt.requestedTimePos.le
  exact
    (complexCoordinateRealInner_intervalIntegrable
      pathContinuous viscousIntegrable).const_mul 2

/-- The work restored from endpoint transport and viscous payment is exactly
the interval integral of the actual whole bilinear coefficient.  The proof
uses the receipt's own unforced tangent law on its common-time carrier. -/
theorem actualWholeRowNonlinearWork_eq_bilinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    actualWholeRowNonlinearWork receipt wave =
      actualWholeRowBilinearWork receipt wave := by
  by_cases waveZero : wave = 0
  · simp [actualWholeRowNonlinearWork,
      actualWholeRowNetWork, actualWholeRowViscousPayment,
      actualWholeRowBilinearWork, waveZero]
  · let path := receipt.rowExtension wave waveZero
    let tangent :=
      commonTimeZeroExtension requestedTime
        (receipt.rowTangent wave waveZero)
    let nonlinear :=
      commonTimeZeroExtension requestedTime
        (fun time =>
          wholeStateVorticityBilinearCoefficientAt
            (receipt.transverseLimit time).1
            (receipt.transverseLimit time).1 wave)
    let viscousCoefficient :=
      ν.coeff * integerWaveViscousMultiplier wave
    let netPower := fun actual =>
      2 * complexCoordinateRealInner
        (path actual) (tangent actual)
    let viscousPower := fun actual =>
      2 * complexCoordinateRealInner
        (path actual) (viscousCoefficient • path actual)
    let nonlinearPower := fun actual =>
      2 * complexCoordinateRealInner
        (path actual) (nonlinear actual)
    have netIntegrable :
        IntervalIntegrable netPower volume 0 requestedTime := by
      exact actualWholeRowNetPower_intervalIntegrable
        receipt wave waveZero
    have viscousIntegrable :
        IntervalIntegrable viscousPower volume 0 requestedTime := by
      exact actualWholeRowViscousPower_intervalIntegrable
        receipt wave waveZero
    have nonlinearIntegral_eq_add :
        (∫ actual in (0 : ℝ)..requestedTime,
            nonlinearPower actual) =
          ∫ actual in (0 : ℝ)..requestedTime,
            netPower actual + viscousPower actual := by
      rw [← commonTime_integral_eq_intervalIntegral
          requestedTime receipt.requestedTimePos.le nonlinearPower,
        ← commonTime_integral_eq_intervalIntegral
          requestedTime receipt.requestedTimePos.le
          (fun actual =>
            netPower actual + viscousPower actual)]
      apply integral_congr_ae
      filter_upwards [
        receipt.rowTangent_eq_unforced_ae
          wave waveZero] with time tangentEq
      have pathEq :
          path time.1 = receipt.wholePath time wave := by
        simpa only [path] using
          receipt.rowExtension_on_interval wave waveZero time
      have tangentEqOnInterval :
          tangent time.1 =
            receipt.rowTangent wave waveZero time := by
        exact commonTimeZeroExtension_of_mem
          requestedTime (receipt.rowTangent wave waveZero)
          time.1 time.property
      have nonlinearEqOnInterval :
          nonlinear time.1 =
            wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 wave := by
        exact commonTimeZeroExtension_of_mem
          requestedTime
          (fun time =>
            wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 wave)
          time.1 time.property
      simp only [nonlinearPower, netPower, viscousPower]
      rw [pathEq, tangentEqOnInterval, nonlinearEqOnInterval,
        tangentEq]
      rw [complexCoordinateRealInner_sub_right]
      ring
    have addIntegral :
        (∫ actual in (0 : ℝ)..requestedTime,
            netPower actual + viscousPower actual) =
          (∫ actual in (0 : ℝ)..requestedTime,
              netPower actual) +
            ∫ actual in (0 : ℝ)..requestedTime,
              viscousPower actual := by
      exact intervalIntegral.integral_add
        netIntegrable viscousIntegrable
    unfold actualWholeRowNonlinearWork
      actualWholeRowNetWork
      actualWholeRowViscousPayment
      actualWholeRowBilinearWork
    simp only [dif_neg waveZero]
    change
      (∫ actual in (0 : ℝ)..requestedTime,
          netPower actual) +
          (∫ actual in (0 : ℝ)..requestedTime,
            viscousPower actual) =
        ∫ actual in (0 : ℝ)..requestedTime,
          nonlinearPower actual
    rw [nonlinearIntegral_eq_add, addIntegral]

/-! ## Transport to the generated restart hard gate -/

/-- Literal bilinear work on one finite output inventory. -/
def actualWholeFiniteBilinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) : ℝ :=
  ∑ wave ∈ modes, actualWholeRowBilinearWork receipt wave

theorem actualWholeFiniteNonlinearWork_eq_bilinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFiniteNonlinearWork receipt modes =
      actualWholeFiniteBilinearWork receipt modes := by
  unfold actualWholeFiniteNonlinearWork
    actualWholeFiniteBilinearWork
  apply Finset.sum_congr rfl
  intro wave _waveMem
  exact actualWholeRowNonlinearWork_eq_bilinearWork receipt wave

/-- Literal whole-bilinear work on one generated restart segment. -/
def wholeRestartSegmentBilinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  actualWholeFiniteBilinearWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

theorem wholeRestartSegmentNonlinearWork_eq_bilinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentNonlinearWork initial index radius =
      wholeRestartSegmentBilinearWork initial index radius :=
  actualWholeFiniteNonlinearWork_eq_bilinearWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

/-- Chronological literal whole-bilinear work before a restart boundary. -/
def wholeRestartAccumulatedBilinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentBilinearWork initial index radius

theorem wholeRestartAccumulatedNonlinearWork_eq_bilinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedNonlinearWork initial length radius =
      wholeRestartAccumulatedBilinearWork initial length radius := by
  unfold wholeRestartAccumulatedNonlinearWork
    wholeRestartAccumulatedBilinearWork
  apply Finset.sum_congr rfl
  intro index _indexMem
  exact wholeRestartSegmentNonlinearWork_eq_bilinearWork
    initial index radius

/-- Finite physical-time accumulation now forces unbounded literal
whole-lattice bilinear work, not merely a restored ledger field. -/
theorem elapsedTime_bddAbove_forces_accumulatedBilinearWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedBilinearWork
          initial index.1 index.2) := by
  simpa only [wholeRestartAccumulatedNonlinearWork_eq_bilinearWork]
    using
      elapsedTime_bddAbove_forces_accumulatedNonlinearWork_unbounded
        initial elapsedBounded

/-! ## Pointwise pre-quotient pair table -/

/-- Real continuous functional obtained by fixing the left coefficient row.
It makes preservation of an absolutely summable pair series by the physical
pairing explicit. -/
def complexCoordinateRealInnerRightCLM
    (left : ComplexCoordinateVector) :
    ComplexCoordinateVector →L[ℝ] ℝ :=
  ∑ coordinate : Coordinate,
    ((left coordinate).re •
        (Complex.reCLM.comp
          (ContinuousLinearMap.proj coordinate :
            ComplexCoordinateVector →L[ℝ] ℂ)) +
      (left coordinate).im •
        (Complex.imCLM.comp
          (ContinuousLinearMap.proj coordinate :
            ComplexCoordinateVector →L[ℝ] ℂ)))

@[simp] theorem complexCoordinateRealInnerRightCLM_apply
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInnerRightCLM left right =
      complexCoordinateRealInner left right := by
  simp [complexCoordinateRealInnerRightCLM,
    complexCoordinateRealInner]

/-- The physical row pairing commutes with every absolutely summable vector
series. -/
theorem complexCoordinateRealInner_tsum_right
    {ι : Type*}
    (left : ComplexCoordinateVector)
    (right : ι → ComplexCoordinateVector)
    (rightSummable : Summable right) :
    complexCoordinateRealInner left (∑' index, right index) =
      ∑' index, complexCoordinateRealInner left (right index) := by
  calc
    complexCoordinateRealInner left (∑' index, right index) =
        complexCoordinateRealInnerRightCLM left
          (∑' index, right index) := by
      rw [complexCoordinateRealInnerRightCLM_apply]
    _ = ∑' index,
          complexCoordinateRealInnerRightCLM left (right index) :=
      (complexCoordinateRealInnerRightCLM left).map_tsum
        rightSummable
    _ = ∑' index,
          complexCoordinateRealInner left (right index) := by
      apply tsum_congr
      intro index
      rw [complexCoordinateRealInnerRightCLM_apply]

/-- One source-owned physical pair occurrence before the fixed-output
Fourier series is aggregated.  Its identity is the actual
`(output, first, output-first, time)` tuple. -/
def actualWholePairPower
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) : ℝ :=
  2 * complexCoordinateRealInner
    (receipt.wholePath time output)
    (finiteStateVorticityBilinearPairContribution
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).1
      (first, output - first))

/-- At every actual common time, the occurrence table is summable.  This is
generated by the fixed-output absolute pair theorem and the literal physical
pairing; no occurrence-weight certificate is supplied. -/
theorem summable_actualWholePairPower
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    Summable fun first : IntegerWavevector =>
      actualWholePairPower receipt output first time := by
  have vectorSummable :
      Summable fun first : IntegerWavevector =>
        finiteStateVorticityBilinearPairContribution
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1
          (first, output - first) :=
    summable_wholeStateVorticityBilinearPair
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).2 output
  have pairedSummable :=
    (complexCoordinateRealInnerRightCLM
      (receipt.wholePath time output)).summable vectorSummable
  exact (pairedSummable.mul_left 2).congr fun first => by
    simp [actualWholePairPower]

/-- Projection of the complete occurrence table is exactly the actual whole
bilinear power at that output and time.  Cancellation is permitted only in
this final `tsum`; occurrence identities exist before it. -/
theorem tsum_actualWholePairPower_eq_bilinearPower
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    (∑' first : IntegerWavevector,
        actualWholePairPower receipt output first time) =
      2 * complexCoordinateRealInner
        (receipt.wholePath time output)
        (wholeStateVorticityBilinearCoefficientAt
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1 output) := by
  have vectorSummable :
      Summable fun first : IntegerWavevector =>
        finiteStateVorticityBilinearPairContribution
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1
          (first, output - first) :=
    summable_wholeStateVorticityBilinearPair
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).2 output
  unfold actualWholePairPower
  rw [tsum_mul_left]
  rw [← complexCoordinateRealInner_tsum_right
    (receipt.wholePath time output) _ vectorSummable]
  rfl

/-- Work obtained by integrating the complete occurrence `tsum` while the
pair index is still present.  This is consume-before-quotient; it does not
assign a separate metric energy to provenance. -/
def actualWholeRowPreQuotientWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) : ℝ :=
  if _outputZero : output = 0 then
    0
  else
    ∫ actual in (0 : ℝ)..requestedTime,
      commonTimeZeroExtension requestedTime
        (fun time =>
          ∑' first : IntegerWavevector,
            actualWholePairPower receipt output first time)
        actual

/-- The pre-quotient occurrence table projects exactly to the literal
bilinear row work. -/
theorem actualWholeRowPreQuotientWork_eq_bilinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    actualWholeRowPreQuotientWork receipt output =
      actualWholeRowBilinearWork receipt output := by
  by_cases outputZero : output = 0
  · simp [actualWholeRowPreQuotientWork,
      actualWholeRowBilinearWork, outputZero]
  · unfold actualWholeRowPreQuotientWork
      actualWholeRowBilinearWork
    simp only [dif_neg outputZero]
    apply intervalIntegral.integral_congr
    intro actual actualMem
    have actualIn : actual ∈ Icc (0 : ℝ) requestedTime := by
      simpa only [uIcc_of_le receipt.requestedTimePos.le] using
        actualMem
    let time : Icc (0 : ℝ) requestedTime := ⟨actual, actualIn⟩
    rw [commonTimeZeroExtension_of_mem
      requestedTime
      (fun time =>
        ∑' first : IntegerWavevector,
          actualWholePairPower receipt output first time)
      actual actualIn]
    change
      (∑' first : IntegerWavevector,
          actualWholePairPower receipt output first time) =
        2 * complexCoordinateRealInner
          (receipt.rowExtension output outputZero actual)
          (commonTimeZeroExtension requestedTime
            (fun time =>
              wholeStateVorticityBilinearCoefficientAt
                (receipt.transverseLimit time).1
                (receipt.transverseLimit time).1 output)
            actual)
    rw [commonTimeZeroExtension_of_mem
      requestedTime
      (fun time =>
        wholeStateVorticityBilinearCoefficientAt
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1 output)
      actual actualIn]
    rw [show
      receipt.rowExtension output outputZero actual =
        receipt.wholePath time output by
      exact receipt.rowExtension_on_interval
        output outputZero time]
    exact tsum_actualWholePairPower_eq_bilinearPower
      receipt output time

/-! ## The hard gate before quotient -/

/-- Finite output inventory whose integrand still carries the complete input
pair occurrence table. -/
def actualWholeFinitePreQuotientWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) : ℝ :=
  ∑ output ∈ modes,
    actualWholeRowPreQuotientWork receipt output

theorem actualWholeFinitePreQuotientWork_eq_bilinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFinitePreQuotientWork receipt modes =
      actualWholeFiniteBilinearWork receipt modes := by
  unfold actualWholeFinitePreQuotientWork
    actualWholeFiniteBilinearWork
  apply Finset.sum_congr rfl
  intro output _outputMem
  exact actualWholeRowPreQuotientWork_eq_bilinearWork
    receipt output

/-- One generated restart segment before the pair quotient. -/
def wholeRestartSegmentPreQuotientWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  actualWholeFinitePreQuotientWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

theorem wholeRestartSegmentPreQuotientWork_eq_bilinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentPreQuotientWork initial index radius =
      wholeRestartSegmentBilinearWork initial index radius :=
  actualWholeFinitePreQuotientWork_eq_bilinearWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

/-- Chronological pre-quotient work table on actual restart occurrences. -/
def wholeRestartAccumulatedPreQuotientWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentPreQuotientWork initial index radius

theorem wholeRestartAccumulatedPreQuotientWork_eq_bilinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedPreQuotientWork initial length radius =
      wholeRestartAccumulatedBilinearWork initial length radius := by
  unfold wholeRestartAccumulatedPreQuotientWork
    wholeRestartAccumulatedBilinearWork
  apply Finset.sum_congr rfl
  intro index _indexMem
  exact wholeRestartSegmentPreQuotientWork_eq_bilinearWork
    initial index radius

/-- Finite-time accumulation forces unbounded work already on the
path-sensitive pair table, before fixed-output aggregation can erase
occurrence provenance. -/
theorem elapsedTime_bddAbove_forces_accumulatedPreQuotientWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedPreQuotientWork
          initial index.1 index.2) := by
  simpa only [wholeRestartAccumulatedPreQuotientWork_eq_bilinearWork]
    using
      elapsedTime_bddAbove_forces_accumulatedBilinearWork_unbounded
        initial elapsedBounded

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
end NavierStokes
end SaturationMonoid
