import H0mework.NavierStokes.PairRestart.PairOccurrenceWork
import H0mework.NavierStokes.ShellSources.ConsumeBeforeQuotient
import H0mework.NavierStokes.ShellGluing.NativeMacroFirstShellPDEBridge

/-!
# Source old-q rows inside whole-flow pair occurrences

The time-integrated occurrence ledger uses an `L²` transverse representative,
whose value at one time is not authoritative.  This module reads the same
pair power from the receipt's continuous whole path, proves a.e. and integral
agreement with the existing ledger, and then identifies its time-zero
nonlinear pair table with the actual macro source's old-`q` table.

No source pair, output, nonzero witness or time window is supplied to the
producer.  The whole path, source and pair table all belong to the same native
macro occurrence.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence

open scoped BigOperators Interval Topology ENNReal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellConsumeBeforeQuotient
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroFirstShellPDEBridge

noncomputable section

private theorem commonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

/-! ## Pointwise whole transverse carrier -/

/-- The continuous whole path cannot leave the closed transverse carrier at
an exceptional time.  Its `L²` representative is transverse almost
everywhere, and every divergence coordinate is continuous on the same
physical interval. -/
theorem wholePath_transverse
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    WholeStateTransverse (receipt.wholePath time) := by
  intro wave
  let extendedDivergence : ℝ → ℂ :=
    fun actual =>
      complexWavevector wave ⬝ᵥ
        receipt.wholePath
          (Set.projIcc
            (0 : ℝ) requestedTime
            receipt.requestedTimePos.le actual) wave
  have extensionContinuous : Continuous extendedDivergence := by
    exact
      continuous_const.dotProduct
        ((lp.evalCLM ℂ
            (fun _ : IntegerWavevector =>
              ComplexCoordinateVector)
            2 wave).continuous.comp
          (receipt.wholePath.continuous.comp
            continuous_projIcc))
  have zeroSubtype :
      ∀ᵐ actual ∂(commonTimeMeasure requestedTime),
        complexWavevector wave ⬝ᵥ
            receipt.wholePath actual wave =
          0 := by
    filter_upwards [receipt.wholePath_eq_transverse_ae] with
      actual pathEq
    rw [pathEq]
    exact (receipt.transverseLimit actual).2 wave
  rw [commonTimeMeasure_eq_comap_volume] at zeroSubtype
  have extensionZeroAE :
      ∀ᵐ actual ∂volume.restrict
          (Icc (0 : ℝ) requestedTime),
        extendedDivergence actual = 0 := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [zeroSubtype] with actual zeroAt
    simpa only [extendedDivergence,
      Set.projIcc_of_mem receipt.requestedTimePos.le
        actual.property] using zeroAt
  have extensionZeroOn :=
    Measure.eqOn_Icc_of_ae_eq
      (μ := volume)
      receipt.requestedTimePos.ne
      extensionZeroAE
      extensionContinuous.continuousOn
      continuousOn_const
  have zeroAtTime := extensionZeroOn time.property
  simpa only [extendedDivergence,
    Set.projIcc_of_mem receipt.requestedTimePos.le
      time.property] using zeroAtTime

/-- Continuous real-line projection of the actual whole path into its
genuine transverse carrier.  Outside the physical interval `projIcc` only
supplies a proof extension; on the interval this is literally `wholePath`. -/
def actualWholeProjectedTransversePath
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (actual : ℝ) : WholeTransverseVorticityState :=
  ⟨receipt.wholePath
      (Set.projIcc
        (0 : ℝ) requestedTime
        receipt.requestedTimePos.le actual),
    wholePath_transverse receipt
      (Set.projIcc
        (0 : ℝ) requestedTime
        receipt.requestedTimePos.le actual)⟩

theorem actualWholeProjectedTransversePath_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    Continuous (actualWholeProjectedTransversePath receipt) := by
  exact
    (receipt.wholePath.continuous.comp continuous_projIcc).subtype_mk
      (fun actual =>
        wholePath_transverse receipt
          (Set.projIcc
            (0 : ℝ) requestedTime
            receipt.requestedTimePos.le actual))

/-- The actual infinite nonlinear output row read from the continuous whole
path before its `L¹` quotient representative is formed. -/
def actualWholeContinuousNonlinearRow
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (actual : ℝ) : ComplexCoordinateVector :=
  wholeStateVorticityNonlinearCoefficientAt
    (actualWholeProjectedTransversePath receipt actual).1 output

theorem actualWholeContinuousNonlinearRow_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    Continuous
      (actualWholeContinuousNonlinearRow receipt output) := by
  exact
    (wholeStateVorticityNonlinearCoefficientAt_continuous output).comp
      (actualWholeProjectedTransversePath_continuous receipt)

/-- The continuous nonlinear row is the same physical row as the receipt's
existing `L¹` representative almost everywhere. -/
theorem actualWholeContinuousNonlinearRow_ae_eq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    (fun time : Icc (0 : ℝ) requestedTime =>
      actualWholeContinuousNonlinearRow receipt output time.1) =ᵐ[
        commonTimeMeasure requestedTime]
      transverseSpaceTimeNonlinearRow
        receipt.transverseLimit output := by
  filter_upwards [
    receipt.wholePath_eq_transverse_ae,
    transverseSpaceTimeNonlinearRow_coeFn
      receipt.transverseLimit output] with
      time pathEq rowEq
  rw [rowEq]
  have projectedEq :
      (actualWholeProjectedTransversePath receipt time.1).1 =
        (receipt.transverseLimit time).1 := by
    change
      receipt.wholePath
          (Set.projIcc
            (0 : ℝ) requestedTime
            receipt.requestedTimePos.le time.1) =
        (receipt.transverseLimit time).1
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      time.property, pathEq]
  exact congrArg
    (fun state : ComplexVorticityHilbertState =>
      wholeStateVorticityNonlinearCoefficientAt state output)
    projectedEq

/-! ## Endpoint FTC on the continuous whole row -/

/-- A continuous nonlinear row gives the integrating-factor path its
classical derivative at every real time, including the source-owned endpoint
`t = 0`.  This is the endpoint strengthening of the existing a.e. derivative
law; no new evolution is introduced. -/
theorem heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
    (initial : ComplexCoordinateVector)
    (nonlinear : ℝ → ComplexCoordinateVector)
    (damping start time : ℝ)
    (nonlinearContinuous : Continuous nonlinear) :
    HasDerivAt
      (heatDuhamelComplexCoordinatePath
        initial nonlinear damping start)
      (nonlinear time -
        damping •
          heatDuhamelComplexCoordinatePath
            initial nonlinear damping start time)
      time := by
  have weightedContinuous :
      Continuous
        (fun actual =>
          Real.exp (damping * (actual - start)) •
            nonlinear actual) := by
    exact
      (by fun_prop :
        Continuous
          (fun actual : ℝ =>
            Real.exp (damping * (actual - start)))).smul
        nonlinearContinuous
  have actualIntegralDerivative :
      HasDerivAt
        (fun actual =>
          ∫ earlier in start..actual,
            Real.exp (damping * (earlier - start)) •
              nonlinear earlier)
        (Real.exp (damping * (time - start)) •
          nonlinear time)
        time :=
    intervalIntegral.integral_hasDerivAt_right
      (weightedContinuous.intervalIntegrable start time)
      (weightedContinuous.stronglyMeasurableAtFilter
        volume (𝓝 time))
      weightedContinuous.continuousAt
  have integralPathDerivative :
      HasDerivAt
        (intervalIntegralComplexCoordinatePath initial
          (fun earlier =>
            Real.exp (damping * (earlier - start)) •
              nonlinear earlier)
          start)
        (Real.exp (damping * (time - start)) •
          nonlinear time)
        time := by
    change
      HasDerivAt
        ((fun _ : ℝ => initial) +
          fun actual =>
            ∫ earlier in start..actual,
              Real.exp (damping * (earlier - start)) •
                nonlinear earlier)
        _
        time
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const time initial).add
        actualIntegralDerivative
  have dampingFactorDerivative :
      HasDerivAt
        (fun actual =>
          Real.exp (-damping * (actual - start)))
        ((-damping) *
          Real.exp (-damping * (time - start)))
        time := by
    have exponentDerivative :
        HasDerivAt
          (fun actual => -damping * (actual - start))
          (-damping) time := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id time).sub_const start).const_mul
          (-damping)
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp
        (-damping * (time - start))).comp
          time exponentDerivative
  have pathDerivative :=
    dampingFactorDerivative.smul integralPathDerivative
  have weightCancellation :
      Real.exp (-damping * (time - start)) *
          Real.exp (damping * (time - start)) =
        1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  change
    HasDerivAt
      ((fun actual =>
          Real.exp (-damping * (actual - start))) •
        intervalIntegralComplexCoordinatePath initial
          (fun earlier =>
            Real.exp (damping * (earlier - start)) •
              nonlinear earlier)
          start)
      (nonlinear time -
        damping •
          (Real.exp (-damping * (time - start)) •
            intervalIntegralComplexCoordinatePath initial
              (fun earlier =>
                Real.exp (damping * (earlier - start)) •
                  nonlinear earlier)
              start time))
      time
  have derivativeEq :
      Real.exp (-damping * (time - start)) •
            (Real.exp (damping * (time - start)) •
              nonlinear time) +
          ((-damping) *
            Real.exp (-damping * (time - start))) •
            intervalIntegralComplexCoordinatePath initial
              (fun earlier =>
                Real.exp (damping * (earlier - start)) •
                  nonlinear earlier)
              start time =
        nonlinear time -
          damping •
            (Real.exp (-damping * (time - start)) •
              intervalIntegralComplexCoordinatePath initial
                (fun earlier =>
                  Real.exp (damping * (earlier - start)) •
                    nonlinear earlier)
                start time) := by
    rw [smul_smul, weightCancellation, one_smul,
      smul_smul]
    module
  rw [← derivativeEq]
  exact pathDerivative

/-- Real-line heat/Duhamel path driven by the receipt's own continuous whole
nonlinear row. -/
def actualWholeContinuousHeatDuhamelPath
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath
    (initialState wave)
    (actualWholeContinuousNonlinearRow receipt wave)
    (ν.coeff * integerWaveViscousMultiplier wave) 0

/-- On the physical interval, the receipt's actual whole row is exactly the
heat/Duhamel path driven by its continuous pre-quotient nonlinear row.  This
is the commuting bridge from the existing `L¹` mild identity to the
authoritative endpoint representative. -/
theorem wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    receipt.wholePath time wave =
      actualWholeContinuousHeatDuhamelPath
        receipt wave time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime receipt.requestedTimePos.le time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier) wave •
          actualWholeContinuousNonlinearRow
            receipt wave earlier)
  have convertedIntegral' :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave earlier
          ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier) wave •
            actualWholeContinuousNonlinearRow
              receipt wave earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    have nonlinearAE :=
      (actualWholeContinuousNonlinearRow_ae_eq
        receipt wave).filter_mono
          (ae_restrict_le (s := Iic time))
    filter_upwards [nonlinearAE] with earlier nonlinearEq
    rw [nonlinearEq]
  rw [receipt.row_mild_identity wave waveNonzero time]
  unfold fixedWaveHeatDuhamelValue
    actualWholeContinuousHeatDuhamelPath
  rw [convertedIntegral']
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

theorem actualWholeContinuousNonlinearRow_zero
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    actualWholeContinuousNonlinearRow receipt output 0 =
      wholeStateVorticityNonlinearCoefficientAt
        initialState output := by
  have stateAtZero :
      (actualWholeProjectedTransversePath receipt 0).1 =
        initialState := by
    change
      receipt.wholePath
          (Set.projIcc
            (0 : ℝ) requestedTime
            receipt.requestedTimePos.le 0) =
        initialState
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      ⟨le_rfl, receipt.requestedTimePos.le⟩]
    exact receipt.wholePath_initial
  exact congrArg
    (fun state : ComplexVorticityHilbertState =>
      wholeStateVorticityNonlinearCoefficientAt state output)
    stateAtZero

/-- The source endpoint derivative of the actual whole row is determined by
the whole nonlinear row and the literal initial viscous row. -/
theorem actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath receipt wave)
      (wholeStateVorticityNonlinearCoefficientAt
          initialState wave -
        (ν.coeff * integerWaveViscousMultiplier wave) •
          initialState wave)
      0 := by
  have generated :=
    heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
      (initialState wave)
      (actualWholeContinuousNonlinearRow receipt wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0 0
      (actualWholeContinuousNonlinearRow_continuous
        receipt wave)
  rw [actualWholeContinuousNonlinearRow_zero
    receipt wave] at generated
  have pathAtZero :
      heatDuhamelComplexCoordinatePath
          (initialState wave)
          (actualWholeContinuousNonlinearRow receipt wave)
          (ν.coeff * integerWaveViscousMultiplier wave)
          0 0 =
        initialState wave := by
    unfold heatDuhamelComplexCoordinatePath
      intervalIntegralComplexCoordinatePath
    simp
  rw [pathAtZero] at generated
  simpa only [actualWholeContinuousHeatDuhamelPath] using generated

/-! ## Continuous representative of the same occurrence -/

/-- The actual pair power read entirely from the receipt's continuous whole
path.  Unlike an `L²` representative, this function has an authoritative
time-zero value. -/
def actualWholeContinuousPairPower
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
    (finiteStateVorticityNonlinearPairContribution
      (receipt.wholePath time) (first, output - first))

theorem actualWholeContinuousPairPower_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector) :
    Continuous
      (actualWholeContinuousPairPower receipt output first) := by
  have outputContinuous :
      Continuous (fun state : ComplexVorticityHilbertState =>
        state output) :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 output).continuous
  have nonlinearContinuous :
      Continuous (fun state : ComplexVorticityHilbertState =>
        finiteStateVorticityNonlinearPairContribution
          state (first, output - first)) :=
    (finiteStateVorticityNonlinearPairContribution_contDiff
      (first, output - first)).continuous
  have statePowerContinuous :
      Continuous (fun state : ComplexVorticityHilbertState =>
        2 * complexCoordinateRealInner
          (state output)
          (finiteStateVorticityNonlinearPairContribution
            state (first, output - first))) :=
    continuous_const.mul
      (complexCoordinateRealInner_prod_continuous.comp
        (outputContinuous.prodMk nonlinearContinuous))
  exact statePowerContinuous.comp receipt.wholePath.continuous

/-- The continuous and transverse occurrence representatives are the same
physical readout almost everywhere on the receipt's own time carrier. -/
theorem actualWholeContinuousPairPower_ae_eq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector) :
    actualWholeContinuousPairPower receipt output first =ᵐ[
        commonTimeMeasure requestedTime]
      actualWholePairPower receipt output first := by
  filter_upwards [receipt.wholePath_eq_transverse_ae] with time pathEq
  unfold actualWholeContinuousPairPower actualWholePairPower
  rw [bilinearPair_self_eq_nonlinearPair, ← pathEq]

/-- Replacing the `L²` representative by the continuous path changes no
time-integrated occurrence work. -/
theorem integral_actualWholeContinuousPairPower_eq_occurrenceWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector) :
    (∫ time,
        actualWholeContinuousPairPower
          receipt output first time
        ∂(commonTimeMeasure requestedTime)) =
      actualWholePairOccurrenceWork receipt output first := by
  unfold actualWholePairOccurrenceWork
  exact integral_congr_ae
    (actualWholeContinuousPairPower_ae_eq
      receipt output first)

/-! ## Exact source pair table at time zero -/

/-- Pair-vector readout of the same continuous whole path.  The scalar work
above is obtained only after pairing this vector with the output row. -/
def actualWholeContinuousPairVector
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  finiteStateVorticityNonlinearPairContribution
    (receipt.wholePath time) (first, output - first)

/-- Nonzero time-integrated work of one exact pair occurrence contains a
nonzero continuous pair vector on the same receipt.  The time is generated
from the continuous representative; no value of an `L²` representative is
selected by the caller. -/
theorem actualWholePairOccurrenceWork_ne_zero_generates_pairVector
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (output first : IntegerWavevector)
    (workNonzero :
      actualWholePairOccurrenceWork receipt output first ≠ 0) :
    ∃ time : Icc (0 : ℝ) requestedTime,
      actualWholeContinuousPairVector receipt output first time ≠ 0 := by
  by_contra noTime
  simp only [not_exists, not_ne_iff] at noTime
  apply workNonzero
  rw [← integral_actualWholeContinuousPairPower_eq_occurrenceWork]
  have powerZero :
      actualWholeContinuousPairPower receipt output first = 0 := by
    funext time
    have vectorZero := noTime time
    unfold actualWholeContinuousPairVector at vectorZero
    unfold actualWholeContinuousPairPower
    rw [vectorZero]
    simp [complexCoordinateRealInner]
  rw [powerZero]
  simp

/-- The finite-state nonlinear pair formula on a generated physical source
is literally the source-owned pair producer, including pairs outside support
whose generated coefficients vanish. -/
theorem finiteStateNonlinearPair_generatedPhysicalSource
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    finiteStateVorticityNonlinearPairContribution
        (generatedComplexVorticityState source
          (generatedSupport source))
        pair =
      generatedVorticityNonlinearPairContribution source pair := by
  by_cases firstMem : pair.1 ∈ generatedSupport source
  · by_cases secondMem : pair.2 ∈ generatedSupport source
    · simp [finiteStateVorticityNonlinearPairContribution,
        finiteStateVelocityCoefficient,
        generatedVorticityNonlinearPairContribution,
        generatedStretchingPairContribution,
        generatedVorticityAdvectionPairContribution,
        generatedVelocityCoefficient,
        generatedComplexVorticityState_apply,
        firstMem, secondMem]
    · simp [finiteStateVorticityNonlinearPairContribution,
        finiteStateVelocityCoefficient,
        generatedVorticityNonlinearPairContribution,
        generatedStretchingPairContribution,
        generatedVorticityAdvectionPairContribution,
        generatedVelocityCoefficient,
        generatedComplexVorticityState_apply,
        generatedVorticityCoefficient_eq_zero_of_not_mem source secondMem,
        firstMem, secondMem]
  · simp [finiteStateVorticityNonlinearPairContribution,
      finiteStateVelocityCoefficient,
      generatedVorticityNonlinearPairContribution,
      generatedStretchingPairContribution,
      generatedVorticityAdvectionPairContribution,
      generatedVelocityCoefficient,
      generatedComplexVorticityState_apply,
      generatedVorticityCoefficient_eq_zero_of_not_mem source firstMem,
      firstMem]

/-- At the source-facing start of a native whole receipt, every input pair is
exactly the old physical source's generated nonlinear pair. -/
theorem generatedNativeMacroWholeReceipt_pairVector_initial
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    actualWholeContinuousPairVector
        (generatedNativeMacroWholeRestartCurrentAt
          lineage index).receipt
        output first
        ⟨0, ⟨le_rfl,
          (generatedNativeMacroWholeRestartCurrentAt
            lineage index).receipt.requestedTimePos.le⟩⟩ =
      generatedVorticityNonlinearPairContribution
        (lineage.current index).physicalSource
        (first, output - first) := by
  unfold actualWholeContinuousPairVector
  rw [(generatedNativeMacroWholeRestartCurrentAt
    lineage index).receipt.wholePath_initial]
  change
    finiteStateVorticityNonlinearPairContribution
        (recollectedPhysicalState (lineage.current index))
        (first, output - first) = _
  rw [recollectedPhysicalState_eq_generatedPhysicalSource]
  exact finiteStateNonlinearPair_generatedPhysicalSource
    (lineage.current index).physicalSource
    (first, output - first)

/-- The complete continuous whole-receipt pair table at time zero is the
actual old-`q` output row generated by that macro source. -/
theorem generatedNativeMacroWholeReceipt_pairTsum_initial
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    (∑' first : IntegerWavevector,
      actualWholeContinuousPairVector
        (generatedNativeMacroWholeRestartCurrentAt
          lineage index).receipt
        output first
        ⟨0, ⟨le_rfl,
          (generatedNativeMacroWholeRestartCurrentAt
            lineage index).receipt.requestedTimePos.le⟩⟩) =
      generatedVorticityNonlinearCoefficientAt
        (lineage.current index).physicalSource output := by
  calc
    (∑' first : IntegerWavevector,
      actualWholeContinuousPairVector
        (generatedNativeMacroWholeRestartCurrentAt
          lineage index).receipt
        output first
        ⟨0, ⟨le_rfl,
          (generatedNativeMacroWholeRestartCurrentAt
            lineage index).receipt.requestedTimePos.le⟩⟩) =
        ∑' first : IntegerWavevector,
          generatedVorticityNonlinearPairContribution
            (lineage.current index).physicalSource
            (first, output - first) := by
      apply tsum_congr
      intro first
      exact generatedNativeMacroWholeReceipt_pairVector_initial
        lineage index output first
    _ = wholeStateVorticityNonlinearCoefficientAt
          (generatedComplexVorticityState
            (lineage.current index).physicalSource
            (generatedSupport
              (lineage.current index).physicalSource))
          output := by
      rw [wholeStateVorticityNonlinearCoefficientAt]
      apply tsum_congr
      intro first
      exact
        (finiteStateNonlinearPair_generatedPhysicalSource
          (lineage.current index).physicalSource
          (first, output - first)).symm
    _ = generatedVorticityNonlinearCoefficientAt
          (lineage.current index).physicalSource output :=
      wholeStateNonlinearCoefficient_generatedSource
        (lineage.current index).physicalSource output

/-! ## Producer-owned first-shell alignment -/

/-- Every native macro edge either has a genuinely quiet old shell trace, or
its first source-generated receipt is simultaneously visible as the nonzero
time-zero pair `tsum` of the same whole receipt.  The active branch, receipt,
outputs and nonzero facts are all produced internally. -/
theorem generatedFirstShellTrace_wholePairOccurrence_initial
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (lineage.step index).shellTrace = 0 ∨
      ((lineage.step index).shellTrace ≠ 0 ∧
        ∃ receipt : GeneratedIntegerShellReceipt,
          receipt.current =
              (lineage.current index).physicalSource ∧
            receipt.wholeShellModes.Nonempty ∧
            ∀ output ∈ receipt.wholeShellModes,
              (∑' first : IntegerWavevector,
                actualWholeContinuousPairVector
                  (generatedNativeMacroWholeRestartCurrentAt
                    lineage index).receipt
                  output first
                  ⟨0, ⟨le_rfl,
                    (generatedNativeMacroWholeRestartCurrentAt
                      lineage index).receipt.requestedTimePos.le⟩⟩) =
                    generatedVorticityNonlinearCoefficientAt
                      (lineage.current index).physicalSource output ∧
                generatedVorticityNonlinearCoefficientAt
                    (lineage.current index).physicalSource output ≠ 0 ∧
                (∀ coordinate,
                  generatedIntegerShellReceiptTrace receipt
                      (output, coordinate) =
                    generatedVorticityNonlinearCoefficientAt
                      (lineage.current index).physicalSource
                      output coordinate)) := by
  rcases generatedFirstShellTrace_actualUnforcedPDE lineage index with
    traceZero | active
  · exact Or.inl traceZero
  · rcases active with
      ⟨traceNonzero, receipt, currentEq, shellNonempty, eachOutput⟩
    refine Or.inr
      ⟨traceNonzero, receipt, currentEq, shellNonempty, ?_⟩
    intro output outputMem
    rcases eachOutput output outputMem with
      ⟨_activeNonlive, _initialZero, _rowDerivative,
        rowNonzero, traceEq, _residualZero⟩
    exact
      ⟨generatedNativeMacroWholeReceipt_pairTsum_initial
          lineage index output,
        rowNonzero, traceEq⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
end NavierStokes
end SaturationMonoid
