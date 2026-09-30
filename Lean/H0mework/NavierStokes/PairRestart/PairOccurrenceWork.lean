import H0mework.NavierStokes.Restart.PreQuotientNonlinearWork

/-!
# Time-integrated pair occurrences on the native whole restart chain

The pointwise pre-quotient table is already absolutely summable in its input
pair index.  Here the existing fixed-output absolute-pair estimate and the
actual whole receipt's `L²_t(ℓ²)` carrier generate an integrable
`L¹_t(ℓ¹_pair)` envelope.  This licenses time/pair Fubini and turns each
`(segment, output, first, output-first)` row into a physical work occurrence.

No occurrence norm is postulated: the envelope is proved from the physical
pair contribution, receipt path and transverse space-time state.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork

open scoped BigOperators Interval Topology ENNReal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-! ## Source-generated `L¹_t(ℓ¹_pair)` envelope -/

/-- Sup-norm form of Cauchy--Schwarz on the actual three-coordinate pairing.
The fixed factor comes only from comparing the Euclidean coefficient energy
with the existing sup-norm carrier. -/
theorem abs_complexCoordinateRealInner_le_three_mul_norm
    (left right : ComplexCoordinateVector) :
    |complexCoordinateRealInner left right| ≤
      3 * ‖left‖ * ‖right‖ := by
  have rightNonneg : 0 ≤ 3 * ‖left‖ * ‖right‖ := by
    positivity
  apply (sq_le_sq₀ (abs_nonneg _) rightNonneg).mp
  rw [sq_abs]
  calc
    complexCoordinateRealInner left right ^ 2 ≤
        complexCoordinateAmplitudeSq left *
          complexCoordinateAmplitudeSq right :=
      complexCoordinateRealInner_sq_le left right
    _ ≤ (3 * ‖left‖ ^ 2) * (3 * ‖right‖ ^ 2) := by
      exact mul_le_mul
        (_root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.complexCoordinateAmplitudeSq_le_three_mul_norm_sq left)
        (_root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.complexCoordinateAmplitudeSq_le_three_mul_norm_sq right)
        (complexCoordinateAmplitudeSq_nonneg right)
        (by positivity)
    _ = (3 * ‖left‖ * ‖right‖) ^ 2 := by ring

/-- One physical pair power is controlled by the norm of that same pair
contribution and the actual output coefficient row. -/
theorem norm_actualWholePairPower_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖actualWholePairPower receipt output first time‖ ≤
      6 * ‖receipt.wholePath time output‖ *
        ‖finiteStateVorticityBilinearPairContribution
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1
          (first, output - first)‖ := by
  rw [Real.norm_eq_abs]
  unfold actualWholePairPower
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have innerBound :=
    abs_complexCoordinateRealInner_le_three_mul_norm
      (receipt.wholePath time output)
      (finiteStateVorticityBilinearPairContribution
        (receipt.transverseLimit time).1
        (receipt.transverseLimit time).1
        (first, output - first))
  nlinarith

/-- Absolute summability of the physical pair-power table at every actual
common time. -/
theorem summable_norm_actualWholePairPower
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    Summable fun first : IntegerWavevector =>
      ‖actualWholePairPower receipt output first time‖ := by
  have pairNormSummable :=
    summable_norm_wholeStateVorticityBilinearPair
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).2 output
  apply
    (pairNormSummable.mul_left
      (6 * ‖receipt.wholePath time output‖)).of_nonneg_of_le
  · intro first
    exact norm_nonneg _
  · intro first
    exact norm_actualWholePairPower_le
      receipt output first time

/-- Pointwise `ℓ¹_pair` mass of the physical occurrence table. -/
def actualWholePairPowerMass
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) : ℝ :=
  ∑' first : IntegerWavevector,
    ‖actualWholePairPower receipt output first time‖

/-- The actual absolute occurrence mass is bounded before aggregation by the
fixed-output pair estimate. -/
theorem actualWholePairPowerMass_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    actualWholePairPowerMass receipt output time ≤
      36 * Real.sqrt (integerWaveNormSq output) *
        ‖receipt.wholePath time output‖ *
        ‖(receipt.transverseLimit time).1‖ ^ 2 := by
  have pairNormSummable :=
    summable_norm_wholeStateVorticityBilinearPair
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).2 output
  have powerNormSummable :=
    summable_norm_actualWholePairPower receipt output time
  calc
    actualWholePairPowerMass receipt output time ≤
        ∑' first : IntegerWavevector,
          6 * ‖receipt.wholePath time output‖ *
            ‖finiteStateVorticityBilinearPairContribution
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1
              (first, output - first)‖ := by
      exact Summable.tsum_le_tsum
        (fun first =>
          norm_actualWholePairPower_le
            receipt output first time)
        powerNormSummable
        (pairNormSummable.mul_left
          (6 * ‖receipt.wholePath time output‖))
    _ = 6 * ‖receipt.wholePath time output‖ *
          (∑' first : IntegerWavevector,
            ‖finiteStateVorticityBilinearPairContribution
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1
              (first, output - first)‖) := by
      rw [tsum_mul_left]
    _ ≤ 6 * ‖receipt.wholePath time output‖ *
          (6 * Real.sqrt (integerWaveNormSq output) *
            ‖(receipt.transverseLimit time).1‖ *
            ‖(receipt.transverseLimit time).1‖) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_norm_wholeStateVorticityBilinearPair_le
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).2 output)
        (by positivity)
    _ = 36 * Real.sqrt (integerWaveNormSq output) *
          ‖receipt.wholePath time output‖ *
          ‖(receipt.transverseLimit time).1‖ ^ 2 := by
      ring

/-- Integrable envelope generated by the actual bounded whole path and the
receipt's transverse `L²_t(ℓ²)` state. -/
def actualWholePairPowerEnvelope
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) : ℝ :=
  36 * Real.sqrt (integerWaveNormSq output) *
    ‖receipt.wholePath‖ * ‖(receipt.transverseLimit time).1‖ ^ 2

theorem actualWholePairPowerMass_le_envelope
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    actualWholePairPowerMass receipt output time ≤
      actualWholePairPowerEnvelope receipt output time := by
  refine (actualWholePairPowerMass_le receipt output time).trans ?_
  have outputNormLeState :
      ‖receipt.wholePath time output‖ ≤
        ‖receipt.wholePath time‖ :=
    lp.norm_apply_le_norm (by norm_num)
      (receipt.wholePath time) output
  have stateNormLePathNorm :
      ‖receipt.wholePath time‖ ≤ ‖receipt.wholePath‖ :=
    receipt.wholePath.norm_coe_le_norm time
  unfold actualWholePairPowerEnvelope
  have coefficientNonneg :
      0 ≤ 36 * Real.sqrt (integerWaveNormSq output) := by
    positivity
  have transverseSqNonneg :
      0 ≤ ‖(receipt.transverseLimit time).1‖ ^ 2 := sq_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (outputNormLeState.trans stateNormLePathNorm)
      coefficientNonneg)
    transverseSqNonneg

/-! ## Time integration before the pair quotient -/

/-- Joint continuity of the actual finite-dimensional coefficient pairing.
This is the measurability seam used before any pair aggregation. -/
theorem complexCoordinateRealInner_prod_continuous :
    Continuous
      (fun pair : ComplexCoordinateVector × ComplexCoordinateVector =>
        complexCoordinateRealInner pair.1 pair.2) := by
  unfold complexCoordinateRealInner
  fun_prop

/-- Every pair occurrence is strongly measurable on the actual common-time
carrier.  The proof uses the receipt's generated a.e. equality between its
continuous whole path and transverse `L²` representative. -/
theorem actualWholePairPower_aestronglyMeasurable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector) :
    AEStronglyMeasurable
      (actualWholePairPower receipt output first)
      (commonTimeMeasure requestedTime) := by
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
  have physicalContinuous :
      Continuous (fun state : ComplexVorticityHilbertState =>
        2 * complexCoordinateRealInner
          (state output)
          (finiteStateVorticityNonlinearPairContribution
            state (first, output - first))) :=
    continuous_const.mul
      (complexCoordinateRealInner_prod_continuous.comp
        (outputContinuous.prodMk nonlinearContinuous))
  have transverseMeasurable :
      AEStronglyMeasurable
        (fun time : Icc (0 : ℝ) requestedTime =>
          (receipt.transverseLimit time).1)
        (commonTimeMeasure requestedTime) :=
    continuous_subtype_val.comp_aestronglyMeasurable
      (MeasureTheory.Lp.aestronglyMeasurable
        receipt.transverseLimit)
  apply
    (physicalContinuous.comp_aestronglyMeasurable
      transverseMeasurable).congr
  filter_upwards [receipt.wholePath_eq_transverse_ae] with time pathEq
  simp only [actualWholePairPower,
    bilinearPair_self_eq_nonlinearPair]
  rw [pathEq]

/-- The source-generated envelope is integrable; no caller supplies an
occurrence weight or time cutoff. -/
theorem actualWholePairPowerEnvelope_integrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    Integrable
      (actualWholePairPowerEnvelope receipt output)
      (commonTimeMeasure requestedTime) := by
  have squareIntegrable :
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          ‖(receipt.transverseLimit time).1‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    (MeasureTheory.Lp.memLp receipt.transverseLimit).integrable_norm_pow
      (by norm_num)
  refine (squareIntegrable.const_mul
    (36 * Real.sqrt (integerWaveNormSq output) *
      ‖receipt.wholePath‖)).congr ?_
  filter_upwards with time
  unfold actualWholePairPowerEnvelope
  ring

/-- The pointwise `ℓ¹_pair` mass is measurable before the pair quotient. -/
theorem actualWholePairPowerMass_aestronglyMeasurable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    AEStronglyMeasurable
      (actualWholePairPowerMass receipt output)
      (commonTimeMeasure requestedTime) := by
  unfold actualWholePairPowerMass
  exact
    (AEMeasurable.tsum fun first =>
      (actualWholePairPower_aestronglyMeasurable
        receipt output first).norm.aemeasurable).aestronglyMeasurable

/-- The complete absolute pair table belongs to `L¹` in physical time. -/
theorem actualWholePairPowerMass_integrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    Integrable
      (actualWholePairPowerMass receipt output)
      (commonTimeMeasure requestedTime) := by
  apply Integrable.mono'
    (actualWholePairPowerEnvelope_integrable receipt output)
    (actualWholePairPowerMass_aestronglyMeasurable receipt output)
  filter_upwards with time
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact actualWholePairPowerMass_le_envelope
      receipt output time
  · exact tsum_nonneg fun first => norm_nonneg _

/-- Physical work carried by one generated
`(output, first, output-first)` occurrence over this receipt's actual time
interval. -/
def actualWholePairOccurrenceWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output first : IntegerWavevector) : ℝ :=
  ∫ time,
    actualWholePairPower receipt output first time
    ∂(commonTimeMeasure requestedTime)

/-- Time integration commutes with the complete input-pair series.  This is
the consume-before-quotient theorem: each occurrence is integrated while its
actual pair identity is still present, and only then is the series summed. -/
theorem hasSum_actualWholePairOccurrenceWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    HasSum
      (fun first : IntegerWavevector =>
        actualWholePairOccurrenceWork receipt output first)
      (∫ time,
        ∑' first : IntegerWavevector,
          actualWholePairPower receipt output first time
        ∂(commonTimeMeasure requestedTime)) := by
  apply
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun first time =>
        ‖actualWholePairPower receipt output first time‖)
      (fun first =>
        actualWholePairPower_aestronglyMeasurable
          receipt output first)
  · intro first
    filter_upwards with time
    exact le_rfl
  · filter_upwards with time
    exact summable_norm_actualWholePairPower
      receipt output time
  · change Integrable
      (actualWholePairPowerMass receipt output)
      (commonTimeMeasure requestedTime)
    exact actualWholePairPowerMass_integrable receipt output
  · filter_upwards with time
    exact (summable_actualWholePairPower
      receipt output time).hasSum

theorem tsum_actualWholePairOccurrenceWork_eq_integral
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    (∑' first : IntegerWavevector,
        actualWholePairOccurrenceWork receipt output first) =
      ∫ time,
        ∑' first : IntegerWavevector,
          actualWholePairPower receipt output first time
        ∂(commonTimeMeasure requestedTime) :=
  (hasSum_actualWholePairOccurrenceWork receipt output).tsum_eq

/-- For every nonzero physical output, the time-integrated occurrence table
projects exactly to the existing pre-quotient row work. -/
theorem integral_actualWholePairPower_eq_rowPreQuotientWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    (∫ time,
        ∑' first : IntegerWavevector,
          actualWholePairPower receipt output first time
        ∂(commonTimeMeasure requestedTime)) =
      actualWholeRowPreQuotientWork receipt output := by
  unfold actualWholeRowPreQuotientWork
  rw [dif_neg outputNonzero]
  rw [← commonTime_integral_eq_intervalIntegral
    requestedTime receipt.requestedTimePos.le
    (commonTimeZeroExtension requestedTime
      (fun time =>
        ∑' first : IntegerWavevector,
          actualWholePairPower receipt output first time))]
  apply integral_congr_ae
  filter_upwards with time
  rw [commonTimeZeroExtension_of_mem
    requestedTime
    (fun time =>
      ∑' first : IntegerWavevector,
        actualWholePairPower receipt output first time)
    time.1 time.2]

/-- The sum of typed, time-integrated pair occurrences is exactly the
physical pre-quotient row work. -/
theorem tsum_actualWholePairOccurrenceWork_eq_rowPreQuotientWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    (∑' first : IntegerWavevector,
        actualWholePairOccurrenceWork receipt output first) =
      actualWholeRowPreQuotientWork receipt output := by
  rw [tsum_actualWholePairOccurrenceWork_eq_integral,
    integral_actualWholePairPower_eq_rowPreQuotientWork
      receipt output outputNonzero]

/-! ## Actual restart-chain accumulation -/

/-- Finite output inventory of time-integrated physical pair occurrences.
The output carrier is finite, while every input-pair row remains the complete
whole-lattice `tsum`. -/
def actualWholeFinitePairOccurrenceWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) : ℝ :=
  ∑ output ∈ modes,
    ∑' first : IntegerWavevector,
      actualWholePairOccurrenceWork receipt output first

/-- A punctured finite output inventory is exactly the pre-quotient work
already carried by the whole receipt. -/
theorem actualWholeFinitePairOccurrenceWork_eq_preQuotientWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    actualWholeFinitePairOccurrenceWork receipt modes =
      actualWholeFinitePreQuotientWork receipt modes := by
  unfold actualWholeFinitePairOccurrenceWork
    actualWholeFinitePreQuotientWork
  apply Finset.sum_congr rfl
  intro output outputMem
  exact tsum_actualWholePairOccurrenceWork_eq_rowPreQuotientWork
    receipt output (fun outputZero => by
      subst output
      exact zeroNotMem outputMem)

/-- On every punctured finite inventory, the actual pair-incidence work is
the exact terminal coefficient-mass change plus the same receipt's viscous
payment. -/
theorem
    actualWholeFinitePairOccurrenceWork_eq_terminal_sub_initial_add_viscousPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    actualWholeFinitePairOccurrenceWork receipt modes =
      finiteStateVorticityCoefficientEnstrophy modes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy modes initialState +
        actualWholeFiniteViscousPayment receipt modes := by
  calc
    actualWholeFinitePairOccurrenceWork receipt modes =
        actualWholeFinitePreQuotientWork receipt modes :=
      actualWholeFinitePairOccurrenceWork_eq_preQuotientWork
        receipt modes zeroNotMem
    _ = actualWholeFiniteBilinearWork receipt modes :=
      actualWholeFinitePreQuotientWork_eq_bilinearWork receipt modes
    _ = actualWholeFiniteNonlinearWork receipt modes :=
      (actualWholeFiniteNonlinearWork_eq_bilinearWork
        receipt modes).symm
    _ = actualWholeFiniteNetWork receipt modes +
        actualWholeFiniteViscousPayment receipt modes :=
      (actualWholeFiniteNetWork_add_viscousPayment receipt modes).symm
    _ = finiteStateVorticityCoefficientEnstrophy modes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy modes initialState +
        actualWholeFiniteViscousPayment receipt modes := by
      rw [actualWholeFiniteNetWork_eq_terminal_sub_initial]

theorem zero_not_mem_wholeRestartModes
    (radius : ℕ) :
    (0 : IntegerWavevector) ∉ wholeRestartModes radius := by
  exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius

/-- One native restart segment with every time-integrated pair occurrence
still typed by its output and two input waves. -/
def wholeRestartSegmentPairOccurrenceWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  actualWholeFinitePairOccurrenceWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

theorem wholeRestartSegmentPairOccurrenceWork_eq_preQuotientWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentPairOccurrenceWork initial index radius =
      wholeRestartSegmentPreQuotientWork initial index radius := by
  exact actualWholeFinitePairOccurrenceWork_eq_preQuotientWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)
    (zero_not_mem_wholeRestartModes radius)

/-- Chronological accumulated occurrence work on the actual native restart
chain.  No restart window can charge an occurrence outside its own segment. -/
def wholeRestartAccumulatedPairOccurrenceWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentPairOccurrenceWork initial index radius

theorem wholeRestartAccumulatedPairOccurrenceWork_eq_preQuotientWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedPairOccurrenceWork
        initial length radius =
      wholeRestartAccumulatedPreQuotientWork
        initial length radius := by
  unfold wholeRestartAccumulatedPairOccurrenceWork
    wholeRestartAccumulatedPreQuotientWork
  apply Finset.sum_congr rfl
  intro index _indexMem
  exact wholeRestartSegmentPairOccurrenceWork_eq_preQuotientWork
    initial index radius

/-- If the source-generated restart chain occupies finite accumulated
physical time, then its typed, time-integrated pair-occurrence work is
unbounded.  Thus the finite-time obstruction survives both time integration
and consume-before-quotient occurrence resolution. -/
theorem elapsedTime_bddAbove_forces_accumulatedPairOccurrenceWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedPairOccurrenceWork
          initial index.1 index.2) := by
  simpa only [
    wholeRestartAccumulatedPairOccurrenceWork_eq_preQuotientWork]
    using
      elapsedTime_bddAbove_forces_accumulatedPreQuotientWork_unbounded
        initial elapsedBounded

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
end NavierStokes
end SaturationMonoid
