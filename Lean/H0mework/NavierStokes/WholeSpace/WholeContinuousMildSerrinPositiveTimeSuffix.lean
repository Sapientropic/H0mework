import Mathlib.MeasureTheory.Group.Measure
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinOverlap
import H0mework.NavierStokes.VelocityEndpoint.MacroCausalDuhamel

/-!
# Positive-time suffixes of whole mild/Serrin receipts

An actual unforced whole receipt can be restarted at any strict internal
physical time.  This file first transports its complete time-dependent
carrier along the literal translation `t ↦ start + t`.  The translation is
measure preserving into its actual image; no future path, overlap equality,
or continuation witness is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinPositiveTimeSuffix

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointMacroCausalDuhamel

noncomputable section

/-- Translation of a rebased suffix time into the original physical time
interval. -/
def commonTimeShift
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (_startLe : start ≤ requestedTime) :
    C(Icc (0 : ℝ) (requestedTime - start),
      Icc (0 : ℝ) requestedTime) where
  toFun time :=
    ⟨start + time.1,
      ⟨add_nonneg startNonneg time.2.1, by
        calc
          start + time.1 ≤ start + (requestedTime - start) :=
            add_le_add_right time.2.2 start
          _ = requestedTime := by ring⟩⟩
  continuous_toFun :=
    (continuous_const.add continuous_subtype_val).subtype_mk
      (fun time =>
        ⟨add_nonneg startNonneg time.2.1, by
          calc
            start + time.1 ≤ start + (requestedTime - start) :=
              add_le_add_right time.2.2 start
            _ = requestedTime := by ring⟩)

@[simp] theorem commonTimeShift_apply
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (time : Icc (0 : ℝ) (requestedTime - start)) :
    (commonTimeShift startNonneg startLe time).1 = start + time.1 :=
  rfl

private theorem commonTimeShift_injective
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime) :
    Function.Injective (commonTimeShift startNonneg startLe) := by
  intro left right equality
  apply Subtype.ext
  have valueEq := congrArg
    (fun time : Icc (0 : ℝ) requestedTime => time.1) equality
  exact add_left_cancel valueEq

private theorem commonTimeShift_measurableEmbedding
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime) :
    MeasurableEmbedding (commonTimeShift startNonneg startLe) :=
  (commonTimeShift startNonneg startLe).continuous.measurableEmbedding
    (commonTimeShift_injective startNonneg startLe)

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

private theorem commonTimeMeasure_comap_shift
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime) :
    Measure.comap (commonTimeShift startNonneg startLe)
        (commonTimeMeasure requestedTime) =
      commonTimeMeasure (requestedTime - start) := by
  rw [commonTimeMeasure_eq_comap_volume,
    commonTimeMeasure_eq_comap_volume]
  rw [Measure.comap_comap
    (commonTimeShift_measurableEmbedding startNonneg startLe).measurableSet_image'
    Subtype.val_injective
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image']
  apply Measure.ext
  intro measurableSet measurableSetMeasurable
  let sourceEmbedding :
      MeasurableEmbedding
        (Subtype.val : Icc (0 : ℝ) (requestedTime - start) → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  let shiftedEmbedding :
      MeasurableEmbedding
        (fun time : Icc (0 : ℝ) (requestedTime - start) =>
          start + time.1) :=
    (continuous_const.add continuous_subtype_val).measurableEmbedding
      (by
        intro left right equality
        apply Subtype.ext
        exact add_left_cancel equality)
  change
    (Measure.comap
        (fun time : Icc (0 : ℝ) (requestedTime - start) =>
          start + time.1) volume) measurableSet =
      (Measure.comap
        (Subtype.val :
          Icc (0 : ℝ) (requestedTime - start) → ℝ)
        volume) measurableSet
  rw [Measure.comap_apply _ shiftedEmbedding.injective
      shiftedEmbedding.measurableSet_image' volume measurableSetMeasurable,
    Measure.comap_apply _ sourceEmbedding.injective
      sourceEmbedding.measurableSet_image' volume measurableSetMeasurable]
  have valueImageMeasurable :
      MeasurableSet
        ((Subtype.val :
          Icc (0 : ℝ) (requestedTime - start) → ℝ) ''
            measurableSet) :=
    sourceEmbedding.measurableSet_image' measurableSetMeasurable
  calc
    volume
        ((fun time : Icc (0 : ℝ) (requestedTime - start) =>
          start + time.1) '' measurableSet) =
      volume
        ((fun value : ℝ => start + value) ''
          ((Subtype.val :
            Icc (0 : ℝ) (requestedTime - start) → ℝ) ''
              measurableSet)) := by
        congr 1
        rw [image_image]
    _ = volume
        ((fun value : ℝ => -start + value) ⁻¹'
          ((Subtype.val :
            Icc (0 : ℝ) (requestedTime - start) → ℝ) ''
              measurableSet)) := by
        rw [image_add_left]
    _ = volume
        ((Subtype.val :
          Icc (0 : ℝ) (requestedTime - start) → ℝ) ''
            measurableSet) :=
      (measurePreserving_add_left volume (-start)).measure_preimage
        valueImageMeasurable.nullMeasurableSet

/-- The physical time shift preserves measure exactly into its actual image
inside the original receipt. -/
theorem commonTimeShift_measurePreserving
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime) :
    MeasurePreserving
      (commonTimeShift startNonneg startLe)
      (commonTimeMeasure (requestedTime - start))
      ((commonTimeMeasure requestedTime).restrict
        (Set.range (commonTimeShift startNonneg startLe))) := by
  let embedding := commonTimeShift_measurableEmbedding startNonneg startLe
  refine
    { measurable := embedding.measurable
      map_eq := ?_ }
  rw [← commonTimeMeasure_comap_shift startNonneg startLe]
  exact embedding.map_comap (commonTimeMeasure requestedTime)

/-- Rebase an actual common-time `Lᵖ` value at a physical suffix start. -/
noncomputable def shiftCommonTimeLp
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (value : MeasureTheory.Lp E p (commonTimeMeasure requestedTime)) :
    MeasureTheory.Lp E p
      (commonTimeMeasure (requestedTime - start)) :=
  let imageMeasure :=
    (commonTimeMeasure requestedTime).restrict
      (Set.range (commonTimeShift startNonneg startLe))
  let valueMem :
      MemLp (fun time => value time) p imageMeasure :=
    (MeasureTheory.Lp.memLp value).restrict _
  let imageValue : MeasureTheory.Lp E p imageMeasure :=
    valueMem.toLp (fun time => value time)
  MeasureTheory.Lp.compMeasurePreserving
    (commonTimeShift startNonneg startLe)
    (commonTimeShift_measurePreserving startNonneg startLe)
    imageValue

theorem shiftCommonTimeLp_apply_ae
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (value : MeasureTheory.Lp E p (commonTimeMeasure requestedTime)) :
    ∀ᵐ time ∂(commonTimeMeasure (requestedTime - start)),
      shiftCommonTimeLp startNonneg startLe value time =
        value (commonTimeShift startNonneg startLe time) := by
  let imageMeasure :=
    (commonTimeMeasure requestedTime).restrict
      (Set.range (commonTimeShift startNonneg startLe))
  let valueMem :
      MemLp (fun time => value time) p imageMeasure :=
    (MeasureTheory.Lp.memLp value).restrict _
  let imageValue : MeasureTheory.Lp E p imageMeasure :=
    valueMem.toLp (fun time => value time)
  have composedAE :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      imageValue
      (commonTimeShift_measurePreserving startNonneg startLe)
  have imageAE :
      imageValue =ᵐ[imageMeasure] fun time => value time :=
    valueMem.coeFn_toLp
  have pulledImageAE :=
    imageAE.comp_tendsto
      (commonTimeShift_measurePreserving startNonneg startLe
        |>.quasiMeasurePreserving.tendsto_ae)
  filter_upwards [composedAE, pulledImageAE] with
    time composedEq imageEq
  exact composedEq.trans imageEq

private theorem ae_comp_commonTimeShift
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    {predicate : Icc (0 : ℝ) requestedTime → Prop}
    (eventuallyOriginal :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime), predicate time) :
    ∀ᵐ time ∂(commonTimeMeasure (requestedTime - start)),
      predicate (commonTimeShift startNonneg startLe time) := by
  have onImage :
      ∀ᵐ time ∂
          (commonTimeMeasure requestedTime).restrict
            (Set.range (commonTimeShift startNonneg startLe)),
        predicate time :=
    MeasureTheory.ae_restrict_le eventuallyOriginal
  exact
    (commonTimeShift_measurePreserving startNonneg startLe
      |>.quasiMeasurePreserving.tendsto_ae) onImage

theorem shiftCommonTimeLp_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (value : MeasureTheory.Lp E p (commonTimeMeasure requestedTime)) :
    ‖shiftCommonTimeLp startNonneg startLe value‖ ≤ ‖value‖ := by
  let imageMeasure :=
    (commonTimeMeasure requestedTime).restrict
      (Set.range (commonTimeShift startNonneg startLe))
  let valueMem :
      MemLp (fun time => value time) p imageMeasure :=
    (MeasureTheory.Lp.memLp value).restrict _
  let imageValue : MeasureTheory.Lp E p imageMeasure :=
    valueMem.toLp (fun time => value time)
  change
    ‖MeasureTheory.Lp.compMeasurePreserving
        (commonTimeShift startNonneg startLe)
        (commonTimeShift_measurePreserving startNonneg startLe)
        imageValue‖ ≤ ‖value‖
  rw [MeasureTheory.Lp.norm_compMeasurePreserving,
    MeasureTheory.Lp.norm_toLp,
    MeasureTheory.Lp.norm_def]
  exact ENNReal.toReal_mono
    (MeasureTheory.Lp.memLp value).2.ne
    (eLpNorm_restrict_le
      (fun time => value time) p
      (commonTimeMeasure requestedTime)
      (Set.range (commonTimeShift startNonneg startLe)))

theorem shiftCommonTimeLp_compLpL
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (map : E →L[ℂ] F)
    (value : MeasureTheory.Lp E p (commonTimeMeasure requestedTime)) :
    shiftCommonTimeLp startNonneg startLe
        ((map.compLpL p (commonTimeMeasure requestedTime)) value) =
      (map.compLpL p (commonTimeMeasure (requestedTime - start)))
        (shiftCommonTimeLp startNonneg startLe value) := by
  apply MeasureTheory.Lp.ext
  have shiftedMapAE :=
    shiftCommonTimeLp_apply_ae startNonneg startLe
      ((map.compLpL p (commonTimeMeasure requestedTime)) value)
  have shiftedValueAE :=
    shiftCommonTimeLp_apply_ae startNonneg startLe value
  have originalMapAE :=
    ae_comp_commonTimeShift startNonneg startLe
      (map.coeFn_compLpL value)
  have suffixMapAE :=
    map.coeFn_compLpL
      (shiftCommonTimeLp startNonneg startLe value)
  filter_upwards [
    shiftedMapAE, shiftedValueAE, originalMapAE, suffixMapAE] with
      time shiftedMapEq shiftedValueEq originalMapEq suffixMapEq
  rw [shiftedMapEq, originalMapEq, suffixMapEq, shiftedValueEq]

theorem boundedContinuousFunction_toLp_comp_commonTimeShift
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (path : BoundedContinuousFunction (Icc (0 : ℝ) requestedTime) E) :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure (requestedTime - start)) ℂ
        (path.compContinuous
          (commonTimeShift startNonneg startLe)) =
      shiftCommonTimeLp startNonneg startLe
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ path) := by
  apply MeasureTheory.Lp.ext
  have suffixPathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (requestedTime - start))
      ℂ (path.compContinuous
        (commonTimeShift startNonneg startLe))
  have shiftedAE :=
    shiftCommonTimeLp_apply_ae startNonneg startLe
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ path)
  have originalPathAE :=
    ae_comp_commonTimeShift startNonneg startLe
      (BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime)
        ℂ path)
  filter_upwards [suffixPathAE, shiftedAE, originalPathAE] with
      time suffixPathEq shiftedEq originalPathEq
  rw [suffixPathEq, shiftedEq, originalPathEq]
  rfl

theorem shiftCommonTimeLp_transverseSpaceTimeInclusion
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (state : TransverseSpaceTimeState requestedTime) :
    shiftCommonTimeLp startNonneg startLe
        (transverseSpaceTimeInclusion requestedTime state) =
      transverseSpaceTimeInclusion (requestedTime - start)
        (shiftCommonTimeLp startNonneg startLe state) := by
  exact shiftCommonTimeLp_compLpL startNonneg startLe
    wholeTransverseVorticitySubmodule.subtypeL state

theorem shiftCommonTimeLp_fixedWaveSpaceTimeRestriction
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (wave : IntegerWavevector)
    (state : SpaceTimeState requestedTime) :
    shiftCommonTimeLp startNonneg startLe
        (fixedWaveSpaceTimeRestriction requestedTime wave state) =
      fixedWaveSpaceTimeRestriction (requestedTime - start) wave
        (shiftCommonTimeLp startNonneg startLe state) := by
  exact shiftCommonTimeLp_compLpL startNonneg startLe
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave) state

theorem wholeSpaceTimeVorticityGradientDensity_shift_le
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    wholeSpaceTimeVorticityGradientDensity (requestedTime - start)
        (shiftCommonTimeLp startNonneg startLe state) wave ≤
      wholeSpaceTimeVorticityGradientDensity requestedTime state wave := by
  unfold wholeSpaceTimeVorticityGradientDensity
  rw [← shiftCommonTimeLp_fixedWaveSpaceTimeRestriction
    startNonneg startLe wave state]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (shiftCommonTimeLp_norm_le startNonneg startLe
        (fixedWaveSpaceTimeRestriction requestedTime wave state)))
    (integerWaveNormSq_nonneg wave)

theorem wholeSpaceTimeVorticityGradientDensity_shift_summable
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime state wave) :
    Summable fun wave : IntegerWavevector =>
      wholeSpaceTimeVorticityGradientDensity (requestedTime - start)
        (shiftCommonTimeLp startNonneg startLe state) wave :=
  gradientSummable.of_nonneg_of_le
    (fun wave =>
      wholeSpaceTimeVorticityGradientDensity_nonneg
        (requestedTime - start)
        (shiftCommonTimeLp startNonneg startLe state) wave)
    (wholeSpaceTimeVorticityGradientDensity_shift_le
      startNonneg startLe state)

theorem shiftCommonTimeLp_transverseSpaceTimeNonlinearRow
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (state : TransverseSpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    shiftCommonTimeLp startNonneg startLe
        (transverseSpaceTimeNonlinearRow state wave) =
      transverseSpaceTimeNonlinearRow
        (shiftCommonTimeLp startNonneg startLe state) wave := by
  apply MeasureTheory.Lp.ext
  have shiftedRowAE :=
    shiftCommonTimeLp_apply_ae startNonneg startLe
      (transverseSpaceTimeNonlinearRow state wave)
  have originalRowAE :=
    ae_comp_commonTimeShift startNonneg startLe
      (transverseSpaceTimeNonlinearRow_coeFn state wave)
  have suffixRowAE :=
    transverseSpaceTimeNonlinearRow_coeFn
      (shiftCommonTimeLp startNonneg startLe state) wave
  have shiftedStateAE :=
    shiftCommonTimeLp_apply_ae startNonneg startLe state
  filter_upwards [
    shiftedRowAE, originalRowAE, suffixRowAE, shiftedStateAE] with
      time shiftedRowEq originalRowEq suffixRowEq shiftedStateEq
  rw [shiftedRowEq, originalRowEq, suffixRowEq]
  simp only [transverseSpaceTimeNonlinearRowFunction]
  rw [shiftedStateEq]

private theorem wholeSpaceTimeNonlinearNegativeOneFunction_shift_ae
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (state : TransverseSpaceTimeState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure (requestedTime - start)),
      wholeSpaceTimeNonlinearNegativeOneFunction
          (shiftCommonTimeLp startNonneg startLe state) time =
        wholeSpaceTimeNonlinearNegativeOneFunction state
          (commonTimeShift startNonneg startLe time) := by
  filter_upwards [
    shiftCommonTimeLp_apply_ae startNonneg startLe state] with
      time shiftedStateEq
  let nonlinearAt :
      ↥wholeTransverseVorticitySubmodule →
        ComplexVorticityHilbertState :=
    fun point => by
      classical
      exact
        if gradientSummable :
            Summable fun wave : IntegerWavevector =>
              integerWaveNormSq wave *
                complexCoordinateAmplitudeSq (point.1 wave)
        then
          wholeStateVorticityNonlinearNegativeOneState
            point.1 point.2 gradientSummable
        else 0
  change nonlinearAt
      ((shiftCommonTimeLp startNonneg startLe state) time) =
    nonlinearAt (state (commonTimeShift startNonneg startLe time))
  exact congrArg nonlinearAt shiftedStateEq

private theorem wholeSpaceTimeViscousNegativeOneFunction_shift_ae
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (nu : ℝ)
    (state : SpaceTimeState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure (requestedTime - start)),
      wholeSpaceTimeViscousNegativeOneFunction nu
          (shiftCommonTimeLp startNonneg startLe state) time =
        wholeSpaceTimeViscousNegativeOneFunction nu state
          (commonTimeShift startNonneg startLe time) := by
  filter_upwards [
    shiftCommonTimeLp_apply_ae startNonneg startLe state] with
      time shiftedStateEq
  let viscousAt :
      ComplexVorticityHilbertState →
        ComplexVorticityHilbertState :=
    fun point => by
      classical
      exact
        if gradientSummable :
            Summable fun wave : IntegerWavevector =>
              integerWaveNormSq wave *
                complexCoordinateAmplitudeSq (point wave)
        then
          wholeStateVorticityViscousNegativeOneState
            nu point gradientSummable
        else 0
  change viscousAt
      ((shiftCommonTimeLp startNonneg startLe state) time) =
    viscousAt (state (commonTimeShift startNonneg startLe time))
  exact congrArg viscousAt shiftedStateEq

/-- Absolute continuity is invariant under rebasing the domain by a real
translation.  Mathlib currently exposes the corresponding derivative and
interval-integral translations separately; this is the exact interval form
needed by a physical receipt suffix. -/
theorem absolutelyContinuousOnInterval_comp_const_add
    {X : Type*}
    [PseudoMetricSpace X]
    {function : ℝ → X}
    {start requestedTime : ℝ}
    (startLe : start ≤ requestedTime)
    (continuous :
      AbsolutelyContinuousOnInterval function start requestedTime) :
    AbsolutelyContinuousOnInterval
      (fun time => function (start + time))
      0 (requestedTime - start) := by
  rw [absolutelyContinuousOnInterval_iff] at continuous ⊢
  intro epsilon epsilonPos
  obtain ⟨delta, deltaPos, controls⟩ := continuous epsilon epsilonPos
  refine ⟨delta, deltaPos, ?_⟩
  rintro ⟨count, intervals⟩ within lengthSmall
  let shiftedIntervals : ℕ → ℝ × ℝ :=
    fun index =>
      (start + (intervals index).1,
        start + (intervals index).2)
  have shiftedWithin :
      (count, shiftedIntervals) ∈
        AbsolutelyContinuousOnInterval.disjWithin
          start requestedTime := by
    unfold AbsolutelyContinuousOnInterval.disjWithin at within ⊢
    constructor
    · intro index indexMem
      have endpoints := within.1 index indexMem
      rw [uIcc_of_le (sub_nonneg.mpr startLe)] at endpoints
      rw [uIcc_of_le startLe]
      constructor
      · change
          start + (intervals index).1 ∈ Icc start requestedTime
        constructor <;> linarith [endpoints.1.1, endpoints.1.2]
      · change
          start + (intervals index).2 ∈ Icc start requestedTime
        constructor <;> linarith [endpoints.2.1, endpoints.2.2]
    · intro left leftMem right rightMem indicesNe
      have originalDisjoint :=
        within.2 leftMem rightMem indicesNe
      change
        Disjoint
          (uIoc (intervals left).1 (intervals left).2)
          (uIoc (intervals right).1 (intervals right).2)
        at originalDisjoint
      change
        Disjoint
          (uIoc (shiftedIntervals left).1
            (shiftedIntervals left).2)
          (uIoc (shiftedIntervals right).1
            (shiftedIntervals right).2)
      rw [Set.disjoint_left] at originalDisjoint ⊢
      intro value valueLeft valueRight
      exact originalDisjoint (a := value - start)
        (by
          simpa only [shiftedIntervals, uIoc, mem_Ioc,
            min_add_add_left, max_add_add_left,
            lt_sub_iff_add_lt, sub_le_iff_le_add,
            add_comm] using valueLeft)
        (by
          simpa only [shiftedIntervals, uIoc, mem_Ioc,
            min_add_add_left, max_add_add_left,
            lt_sub_iff_add_lt, sub_le_iff_le_add,
            add_comm] using valueRight)
  have shiftedLengthSmall :
      ∑ index ∈ Finset.range count,
          dist (shiftedIntervals index).1
            (shiftedIntervals index).2 < delta := by
    simpa only [shiftedIntervals, dist_add_left] using lengthSmall
  have shiftedControl :=
    controls (count, shiftedIntervals) shiftedWithin shiftedLengthSmall
  simpa only [shiftedIntervals] using shiftedControl

/-- The heat/Duhamel update itself is invariant under rebasing its physical
clock.  Both sides use the same nonlinear row; only its time coordinate is
translated. -/
theorem heatDuhamelComplexCoordinatePath_rebase
    (initial : ComplexCoordinateVector)
    (nonlinear : ℝ → ComplexCoordinateVector)
    (damping start time : ℝ) :
    heatDuhamelComplexCoordinatePath
        initial (fun localTime => nonlinear (start + localTime))
        damping 0 time =
      heatDuhamelComplexCoordinatePath
        initial nonlinear damping start (start + time) := by
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral,
    heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  apply congrArg₂ (fun left right => left + right)
  · congr 2
    ring
  · have translated :=
      intervalIntegral.integral_comp_add_left
        (fun actual =>
          Real.exp (-damping * ((start + time) - actual)) •
            nonlinear actual)
        (a := (0 : ℝ)) (b := time) start
    simpa only [zero_add, add_zero, add_sub_add_left_eq_sub] using translated

/-- Restarting the same causal row is exactly the original heat/Duhamel
path. -/
theorem heatDuhamelComplexCoordinatePath_restart_same
    (initial : ComplexCoordinateVector)
    (nonlinear : ℝ → ComplexCoordinateVector)
    (damping start time : ℝ)
    (priorIntegrable :
      IntervalIntegrable nonlinear volume 0 start)
    (nextIntegrable :
      IntervalIntegrable nonlinear volume start time) :
    heatDuhamelComplexCoordinatePath
        (heatDuhamelComplexCoordinatePath
          initial nonlinear damping 0 start)
        nonlinear damping start time =
      heatDuhamelComplexCoordinatePath
        initial nonlinear damping 0 time := by
  rw [heatDuhamelComplexCoordinatePath_restart_eq_causal_sum]
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  have priorWeighted :
      IntervalIntegrable
        (fun earlier =>
          Real.exp (-damping * (time - earlier)) • nonlinear earlier)
        volume 0 start :=
    priorIntegrable.continuousOn_smul (by fun_prop)
  have nextWeighted :
      IntervalIntegrable
        (fun earlier =>
          Real.exp (-damping * (time - earlier)) • nonlinear earlier)
        volume start time :=
    nextIntegrable.continuousOn_smul (by fun_prop)
  rw [add_assoc,
    intervalIntegral.integral_add_adjacent_intervals
      priorWeighted nextWeighted]

private theorem shiftCommonTimeZeroExtension_eq_ae
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {start requestedTime : ℝ}
    (startNonneg : 0 ≤ start)
    (startLe : start ≤ requestedTime)
    (value : MeasureTheory.Lp E p (commonTimeMeasure requestedTime)) :
    ∀ᵐ localTime ∂volume,
      localTime ∈ Icc (0 : ℝ) (requestedTime - start) →
        commonTimeZeroExtension (requestedTime - start)
            (shiftCommonTimeLp startNonneg startLe value) localTime =
          commonTimeZeroExtension requestedTime value
            (start + localTime) := by
  have shiftedSubtypeAE :=
    shiftCommonTimeLp_apply_ae startNonneg startLe value
  have shiftedSubtypeAE' :
      ∀ᵐ time ∂
          Measure.comap
            (Subtype.val :
              Icc (0 : ℝ) (requestedTime - start) → ℝ)
            volume,
        shiftCommonTimeLp startNonneg startLe value time =
          value (commonTimeShift startNonneg startLe time) := by
    rw [← commonTimeMeasure_eq_comap_volume]
    exact shiftedSubtypeAE
  have shiftedRestrictedAE :
      ∀ᵐ localTime ∂
          volume.restrict (Icc (0 : ℝ) (requestedTime - start)),
        commonTimeZeroExtension (requestedTime - start)
            (shiftCommonTimeLp startNonneg startLe value) localTime =
          commonTimeZeroExtension requestedTime value
            (start + localTime) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [shiftedSubtypeAE'] with localTime shiftedEq
    have originalMem :
        start + localTime.1 ∈ Icc (0 : ℝ) requestedTime := by
      constructor
      · exact add_nonneg startNonneg localTime.2.1
      · calc
          start + localTime.1 ≤
              start + (requestedTime - start) :=
            add_le_add_right localTime.2.2 start
          _ = requestedTime := by ring
    rw [commonTimeZeroExtension_of_mem
        (requestedTime - start) _ localTime.1 localTime.2,
      commonTimeZeroExtension_of_mem
        requestedTime _ (start + localTime.1) originalMem]
    exact shiftedEq
  exact
    (ae_restrict_iff' measurableSet_Icc).1 shiftedRestrictedAE

/-- A fixed-wave mild write restarts at an internal physical time on the
same actual nonlinear row. -/
theorem fixedWaveHeatDuhamelValue_positiveTimeSuffix
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (start : ℝ)
    (startNonneg : 0 ≤ start)
    (startLt : start < requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) (requestedTime - start)) :
    fixedWaveHeatDuhamelValue (requestedTime - start)
        nu.coeff wave
        (receipt.wholePath
          ⟨start, ⟨startNonneg, startLt.le⟩⟩ wave)
        (transverseSpaceTimeNonlinearRow
          (shiftCommonTimeLp startNonneg startLt.le
            receipt.transverseLimit) wave)
        time =
      receipt.wholePath
        (commonTimeShift startNonneg startLt.le time) wave := by
  let originalRow :=
    transverseSpaceTimeNonlinearRow receipt.transverseLimit wave
  let shiftedRow :=
    transverseSpaceTimeNonlinearRow
      (shiftCommonTimeLp startNonneg startLt.le
        receipt.transverseLimit) wave
  have shiftedRowEq :
      shiftedRow =
        shiftCommonTimeLp startNonneg startLt.le originalRow := by
    exact
      (shiftCommonTimeLp_transverseSpaceTimeNonlinearRow
        startNonneg startLt.le receipt.transverseLimit wave).symm
  rw [show
      transverseSpaceTimeNonlinearRow
          (shiftCommonTimeLp startNonneg startLt.le
            receipt.transverseLimit) wave = shiftedRow by rfl,
    shiftedRowEq]
  rw [fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath
    (requestedTime - start) (sub_nonneg.mpr startLt.le)
    nu.coeff wave
    (receipt.wholePath
      ⟨start, ⟨startNonneg, startLt.le⟩⟩ wave)
    (shiftCommonTimeLp startNonneg startLt.le originalRow) time]
  let originalZero : ℝ → ComplexCoordinateVector :=
    commonTimeZeroExtension requestedTime originalRow
  let suffixZero : ℝ → ComplexCoordinateVector :=
    commonTimeZeroExtension (requestedTime - start)
      (shiftCommonTimeLp startNonneg startLt.le originalRow)
  have zeroEqAE :=
    shiftCommonTimeZeroExtension_eq_ae
      startNonneg startLt.le originalRow
  have suffixHeatEq :
      heatDuhamelComplexCoordinatePath
          (receipt.wholePath
            ⟨start, ⟨startNonneg, startLt.le⟩⟩ wave)
          suffixZero
          (nu.coeff * integerWaveViscousMultiplier wave) 0 time.1 =
        heatDuhamelComplexCoordinatePath
          (receipt.wholePath
            ⟨start, ⟨startNonneg, startLt.le⟩⟩ wave)
          (fun localTime => originalZero (start + localTime))
          (nu.coeff * integerWaveViscousMultiplier wave) 0 time.1 := by
    rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral,
      heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
    apply congrArg₂ (fun left right => left + right)
    · rfl
    · apply intervalIntegral.integral_congr_ae
      filter_upwards [zeroEqAE] with localTime zeroEq
      intro localMem
      have localIcc :
          localTime ∈ Icc (0 : ℝ) (requestedTime - start) := by
        rw [uIoc_of_le time.2.1] at localMem
        exact ⟨localMem.1.le, localMem.2.trans time.2.2⟩
      rw [show suffixZero localTime =
          originalZero (start + localTime) by
        exact zeroEq localIcc]
  rw [suffixHeatEq,
    heatDuhamelComplexCoordinatePath_rebase]
  have originalIntegrable :=
    commonTimeZeroExtension_intervalIntegrable
      requestedTime receipt.requestedTimePos.le originalRow
  have priorIntegrable :
      IntervalIntegrable originalZero volume 0 start := by
    apply IntervalIntegrable.mono_set' originalIntegrable
    rw [uIoc_of_le startNonneg,
      uIoc_of_le receipt.requestedTimePos.le]
    intro actual actualMem
    exact ⟨actualMem.1, actualMem.2.trans startLt.le⟩
  have shiftedTimeLe : start + time.1 ≤ requestedTime := by
    calc
      start + time.1 ≤ start + (requestedTime - start) :=
        add_le_add_right time.2.2 start
      _ = requestedTime := by ring
  have nextIntegrable :
      IntervalIntegrable originalZero volume start
        (start + time.1) := by
    apply IntervalIntegrable.mono_set' originalIntegrable
    rw [uIoc_of_le (le_add_of_nonneg_right time.2.1),
      uIoc_of_le receipt.requestedTimePos.le]
    intro actual actualMem
    exact ⟨startNonneg.trans_lt actualMem.1,
      actualMem.2.trans shiftedTimeLe⟩
  have startMild :=
    receipt.row_mild_identity wave waveNe
      ⟨start, ⟨startNonneg, startLt.le⟩⟩
  have startHeat :
      receipt.wholePath
          ⟨start, ⟨startNonneg, startLt.le⟩⟩ wave =
        heatDuhamelComplexCoordinatePath
          (initialState wave) originalZero
          (nu.coeff * integerWaveViscousMultiplier wave) 0 start := by
    rw [startMild]
    exact fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath
      requestedTime receipt.requestedTimePos.le nu.coeff wave
      (initialState wave) originalRow
      ⟨start, ⟨startNonneg, startLt.le⟩⟩
  rw [startHeat,
    heatDuhamelComplexCoordinatePath_restart_same
      (initialState wave) originalZero
      (nu.coeff * integerWaveViscousMultiplier wave)
      start (start + time.1) priorIntegrable nextIntegrable]
  have endMild :=
    receipt.row_mild_identity wave waveNe
      (commonTimeShift startNonneg startLt.le time)
  rw [endMild]
  exact
    (fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath
      requestedTime receipt.requestedTimePos.le nu.coeff wave
      (initialState wave) originalRow
      (commonTimeShift startNonneg startLt.le time)).symm

/-- The original-time point which becomes time zero of a receipt suffix. -/
def wholeContinuousMildSerrinSuffixStartTime
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (_receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (start : ℝ)
    (startNonneg : 0 ≤ start)
    (startLt : start < requestedTime) :
    Icc (0 : ℝ) requestedTime :=
  ⟨start, ⟨startNonneg, startLt.le⟩⟩

/-- Rebase an actual whole mild/Serrin receipt at a strict internal physical
time.  The new receipt is generated entirely from the original path and its
unforced write law; no target solution or overlap equality enters the mouth. -/
noncomputable def positiveTimeSuffixWholeContinuousMildSerrinReceipt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (start : ℝ)
    (startNonneg : 0 ≤ start)
    (startLt : start < requestedTime) :
    WholeContinuousMildSerrinReceipt nu
      (receipt.wholePath
        (wholeContinuousMildSerrinSuffixStartTime
          receipt start startNonneg startLt))
      (requestedTime - start) := by
  let shiftedState : SpaceTimeState (requestedTime - start) :=
    shiftCommonTimeLp startNonneg startLt.le receipt.stateLimit
  let shiftedTransverse :
      TransverseSpaceTimeState (requestedTime - start) :=
    shiftCommonTimeLp startNonneg startLt.le receipt.transverseLimit
  let shiftedTangent : SpaceTimeState (requestedTime - start) :=
    shiftCommonTimeLp startNonneg startLt.le receipt.wholeTangent
  let shiftedPath :
      BoundedContinuousFunction
        (Icc (0 : ℝ) (requestedTime - start))
        ComplexVorticityHilbertState :=
    receipt.wholePath.compContinuous
      (commonTimeShift startNonneg startLt.le)
  let shiftedRowExtension :
      ∀ wave : IntegerWavevector, wave ≠ 0 →
        ℝ → ComplexCoordinateVector :=
    fun wave waveNe time =>
      receipt.rowExtension wave waveNe (start + time)
  refine
    { requestedTimePos := sub_pos.mpr startLt
      stateLimit := shiftedState
      transverseLimit := shiftedTransverse
      stateLimit_eq_transverse := ?_
      wholePath := shiftedPath
      wholePath_toLp_eq_stateLimit := ?_
      wholePath_initial := ?_
      wholePath_zero_row := ?_
      transverse_fourierReality_ae := ?_
      gradient_summable := ?_
      wholeTangent := shiftedTangent
      wholeTangent_eq_unforced_ae := ?_
      rowExtension := shiftedRowExtension
      rowExtension_on_interval := ?_
      rowTangent := fun wave waveNe time =>
        receipt.rowTangent wave waveNe
          (commonTimeShift startNonneg startLt.le time)
      rowTangent_eq_unforced_ae := ?_
      rowTangent_eq_wholeTangent_ae := ?_
      rowExtension_absolutelyContinuous := ?_
      rowExtension_ae_hasDerivAt := ?_
      row_mild_identity := ?_ }
  · dsimp only [shiftedState, shiftedTransverse]
    rw [← shiftCommonTimeLp_transverseSpaceTimeInclusion]
    exact congrArg
      (shiftCommonTimeLp startNonneg startLt.le)
      receipt.stateLimit_eq_transverse
  · dsimp only [shiftedPath, shiftedState]
    rw [boundedContinuousFunction_toLp_comp_commonTimeShift,
      receipt.wholePath_toLp_eq_stateLimit]
  · dsimp only [shiftedPath]
    apply congrArg receipt.wholePath
    apply Subtype.ext
    simp [commonTimeShift_apply,
      wholeContinuousMildSerrinSuffixStartTime]
  · intro time
    dsimp only [shiftedPath]
    exact receipt.wholePath_zero_row
      (commonTimeShift startNonneg startLt.le time)
  · have originalReality :=
      ae_comp_commonTimeShift startNonneg startLt.le
        receipt.transverse_fourierReality_ae
    have shiftedTransverseAE :=
      shiftCommonTimeLp_apply_ae startNonneg startLt.le
        receipt.transverseLimit
    filter_upwards [originalReality, shiftedTransverseAE] with
        time reality shiftedEq
    dsimp only [shiftedTransverse]
    rw [shiftedEq]
    exact reality
  · exact wholeSpaceTimeVorticityGradientDensity_shift_summable
      startNonneg startLt.le receipt.stateLimit
        receipt.gradient_summable
  · have shiftedTangentAE :=
      shiftCommonTimeLp_apply_ae startNonneg startLt.le
        receipt.wholeTangent
    have originalEquation :=
      ae_comp_commonTimeShift startNonneg startLt.le
        receipt.wholeTangent_eq_unforced_ae
    have nonlinearAE :=
      wholeSpaceTimeNonlinearNegativeOneFunction_shift_ae
        startNonneg startLt.le receipt.transverseLimit
    have viscousAE :=
      wholeSpaceTimeViscousNegativeOneFunction_shift_ae
        startNonneg startLt.le nu.coeff receipt.stateLimit
    filter_upwards [
      shiftedTangentAE, originalEquation, nonlinearAE, viscousAE] with
        time shiftedTangentEq originalEq nonlinearEq viscousEq
    dsimp only [shiftedTangent, shiftedTransverse, shiftedState]
    rw [shiftedTangentEq, originalEq, nonlinearEq, viscousEq]
  · intro wave waveNe time
    dsimp only [shiftedRowExtension, shiftedPath]
    exact receipt.rowExtension_on_interval wave waveNe
      (commonTimeShift startNonneg startLt.le time)
  · intro wave waveNe
    have originalEquation :=
      ae_comp_commonTimeShift startNonneg startLt.le
        (receipt.rowTangent_eq_unforced_ae wave waveNe)
    have shiftedTransverseAE :=
      shiftCommonTimeLp_apply_ae startNonneg startLt.le
        receipt.transverseLimit
    filter_upwards [originalEquation, shiftedTransverseAE] with
        time originalEq shiftedTransverseEq
    dsimp only [shiftedTransverse, shiftedPath]
    rw [originalEq, shiftedTransverseEq]
    rfl
  · intro wave waveNe
    have originalEquation :=
      ae_comp_commonTimeShift startNonneg startLt.le
        (receipt.rowTangent_eq_wholeTangent_ae wave waveNe)
    have shiftedTangentAE :=
      shiftCommonTimeLp_apply_ae startNonneg startLt.le
        receipt.wholeTangent
    filter_upwards [originalEquation, shiftedTangentAE] with
        time originalEq shiftedTangentEq
    dsimp only [shiftedTangent]
    rw [shiftedTangentEq, originalEq]
  · intro wave waveNe
    apply absolutelyContinuousOnInterval_comp_const_add startLt.le
    apply (receipt.rowExtension_absolutelyContinuous wave waveNe).mono
    rw [uIcc_of_le startLt.le,
      uIcc_of_le receipt.requestedTimePos.le]
    exact Icc_subset_Icc startNonneg le_rfl
  · intro wave waveNe
    have translatedDerivative :=
      ((measurePreserving_add_left volume start)
        |>.quasiMeasurePreserving.tendsto_ae)
        (receipt.rowExtension_ae_hasDerivAt wave waveNe)
    filter_upwards [translatedDerivative] with
      localTime originalDerivative
    intro localMem
    have localMemIcc :
        localTime ∈ Icc (0 : ℝ) (requestedTime - start) := by
      simpa only [uIcc_of_le (sub_nonneg.mpr startLt.le)] using localMem
    have originalMem :
        start + localTime ∈ uIcc (0 : ℝ) requestedTime := by
      rw [uIcc_of_le receipt.requestedTimePos.le]
      constructor
      · exact add_nonneg startNonneg localMemIcc.1
      · calc
          start + localTime ≤
              start + (requestedTime - start) :=
            add_le_add_right localMemIcc.2 start
          _ = requestedTime := by ring
    have applied := originalDerivative originalMem
    have shiftedDerivative :=
      applied.comp_const_add start localTime
    have coefficientEq :
        commonTimeZeroExtension requestedTime
            (receipt.rowTangent wave waveNe) (start + localTime) =
          commonTimeZeroExtension (requestedTime - start)
            (fun time =>
              receipt.rowTangent wave waveNe
                (commonTimeShift startNonneg startLt.le time))
            localTime := by
      rw [commonTimeZeroExtension_of_mem
          requestedTime _ (start + localTime)
          (by simpa only [uIcc_of_le receipt.requestedTimePos.le]
            using originalMem),
        commonTimeZeroExtension_of_mem
          (requestedTime - start) _ localTime localMemIcc]
      apply congrArg (receipt.rowTangent wave waveNe)
      apply Subtype.ext
      rfl
    rw [coefficientEq] at shiftedDerivative
    exact shiftedDerivative
  · intro wave waveNe time
    change
      receipt.wholePath
          (commonTimeShift startNonneg startLt.le time) wave = _
    simpa only [wholeContinuousMildSerrinSuffixStartTime] using
      (fixedWaveHeatDuhamelValue_positiveTimeSuffix
        receipt start startNonneg startLt wave waveNe time).symm

@[simp] theorem positiveTimeSuffixWholeContinuousMildSerrinReceipt_wholePath
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (start : ℝ)
    (startNonneg : 0 ≤ start)
    (startLt : start < requestedTime)
    (time : Icc (0 : ℝ) (requestedTime - start)) :
    (positiveTimeSuffixWholeContinuousMildSerrinReceipt
        receipt start startNonneg startLt).wholePath time =
      receipt.wholePath
        (commonTimeShift startNonneg startLt.le time) :=
  rfl

end

end ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinPositiveTimeSuffix
end NavierStokes
end SaturationMonoid
