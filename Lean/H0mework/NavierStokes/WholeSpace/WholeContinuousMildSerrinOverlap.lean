import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness

/-!
# Cross-horizon overlap for whole mild/Serrin receipts

This module restricts one actual whole mild/Serrin receipt to a shorter
physical interval and applies the already closed same-horizon uniqueness
theorem.  The time inclusion is measure preserving only into the restriction
of the larger common-time measure to its actual image; it is never treated as
measure preserving into the whole larger interval.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap

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

noncomputable section

/-- The literal inclusion of a shorter physical time interval into a longer one. -/
def commonTimeInclusion
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig) :
    C(Icc (0 : ℝ) Tsmall, Icc (0 : ℝ) Tbig) where
  toFun time :=
    ⟨time.1, ⟨time.2.1, time.2.2.trans timeLe⟩⟩
  continuous_toFun :=
    continuous_subtype_val.subtype_mk
      (fun time => ⟨time.2.1, time.2.2.trans timeLe⟩)

@[simp] theorem commonTimeInclusion_apply
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (time : Icc (0 : ℝ) Tsmall) :
    (commonTimeInclusion timeLe time).1 = time.1 :=
  rfl

private theorem commonTimeInclusion_injective
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig) :
    Function.Injective (commonTimeInclusion timeLe) := by
  intro left right equality
  apply Subtype.ext
  exact congrArg (fun time : Icc (0 : ℝ) Tbig => time.1) equality

private theorem commonTimeInclusion_measurableEmbedding
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig) :
    MeasurableEmbedding (commonTimeInclusion timeLe) :=
  (commonTimeInclusion timeLe).continuous.measurableEmbedding
    (commonTimeInclusion_injective timeLe)

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

private theorem commonTimeMeasure_comap_inclusion
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig) :
    Measure.comap (commonTimeInclusion timeLe)
        (commonTimeMeasure Tbig) =
      commonTimeMeasure Tsmall := by
  rw [commonTimeMeasure_eq_comap_volume,
    commonTimeMeasure_eq_comap_volume]
  rw [Measure.comap_comap
    (commonTimeInclusion_measurableEmbedding timeLe).measurableSet_image'
    Subtype.val_injective
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image']
  rfl

/--
The shorter-time inclusion preserves measure exactly into its image inside
the larger common-time carrier.
-/
theorem commonTimeInclusion_measurePreserving
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig) :
    MeasurePreserving
      (commonTimeInclusion timeLe)
      (commonTimeMeasure Tsmall)
      ((commonTimeMeasure Tbig).restrict
        (Set.range (commonTimeInclusion timeLe))) := by
  let embedding :=
    commonTimeInclusion_measurableEmbedding timeLe
  refine
    { measurable := embedding.measurable
      map_eq := ?_ }
  rw [← commonTimeMeasure_comap_inclusion timeLe]
  exact embedding.map_comap (commonTimeMeasure Tbig)

/--
Restriction of an actual common-time `Lᵖ` value to a shorter physical
interval.  The intermediate target measure is the larger measure restricted
to the literal image of the time inclusion.
-/
noncomputable def restrictCommonTimeLp
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (value : MeasureTheory.Lp E p (commonTimeMeasure Tbig)) :
    MeasureTheory.Lp E p (commonTimeMeasure Tsmall) :=
  let imageMeasure :=
    (commonTimeMeasure Tbig).restrict
      (Set.range (commonTimeInclusion timeLe))
  let valueMem :
      MemLp (fun time => value time) p imageMeasure :=
    (MeasureTheory.Lp.memLp value).restrict _
  let imageValue : MeasureTheory.Lp E p imageMeasure :=
    valueMem.toLp (fun time => value time)
  MeasureTheory.Lp.compMeasurePreserving
    (commonTimeInclusion timeLe)
    (commonTimeInclusion_measurePreserving timeLe)
    imageValue

theorem restrictCommonTimeLp_apply_ae
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (value : MeasureTheory.Lp E p (commonTimeMeasure Tbig)) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      restrictCommonTimeLp timeLe value time =
        value (commonTimeInclusion timeLe time) := by
  let imageMeasure :=
    (commonTimeMeasure Tbig).restrict
      (Set.range (commonTimeInclusion timeLe))
  let valueMem :
      MemLp (fun time => value time) p imageMeasure :=
    (MeasureTheory.Lp.memLp value).restrict _
  let imageValue : MeasureTheory.Lp E p imageMeasure :=
    valueMem.toLp (fun time => value time)
  have composedAE :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      imageValue
      (commonTimeInclusion_measurePreserving timeLe)
  have imageAE :
      imageValue =ᵐ[imageMeasure] fun time => value time :=
    valueMem.coeFn_toLp
  have pulledImageAE :=
    imageAE.comp_tendsto
      (commonTimeInclusion_measurePreserving timeLe
        |>.quasiMeasurePreserving.tendsto_ae)
  filter_upwards [composedAE, pulledImageAE] with
    time composedEq imageEq
  exact composedEq.trans imageEq

private theorem ae_comp_commonTimeInclusion
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    {predicate : Icc (0 : ℝ) Tbig → Prop}
    (eventuallyBig :
      ∀ᵐ time ∂(commonTimeMeasure Tbig), predicate time) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      predicate (commonTimeInclusion timeLe time) := by
  have onImage :
      ∀ᵐ time ∂
          (commonTimeMeasure Tbig).restrict
            (Set.range (commonTimeInclusion timeLe)),
        predicate time :=
    MeasureTheory.ae_restrict_le eventuallyBig
  exact
    (commonTimeInclusion_measurePreserving timeLe
      |>.quasiMeasurePreserving.tendsto_ae) onImage

theorem restrictCommonTimeLp_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    {p : ℝ≥0∞}
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (value : MeasureTheory.Lp E p (commonTimeMeasure Tbig)) :
    ‖restrictCommonTimeLp timeLe value‖ ≤ ‖value‖ := by
  let imageMeasure :=
    (commonTimeMeasure Tbig).restrict
      (Set.range (commonTimeInclusion timeLe))
  let valueMem :
      MemLp (fun time => value time) p imageMeasure :=
    (MeasureTheory.Lp.memLp value).restrict _
  let imageValue : MeasureTheory.Lp E p imageMeasure :=
    valueMem.toLp (fun time => value time)
  change
    ‖MeasureTheory.Lp.compMeasurePreserving
        (commonTimeInclusion timeLe)
        (commonTimeInclusion_measurePreserving timeLe)
        imageValue‖ ≤
      ‖value‖
  rw [MeasureTheory.Lp.norm_compMeasurePreserving,
    MeasureTheory.Lp.norm_toLp,
    MeasureTheory.Lp.norm_def]
  exact ENNReal.toReal_mono
    (MeasureTheory.Lp.memLp value).2.ne
    (eLpNorm_restrict_le
      (fun time => value time) p
      (commonTimeMeasure Tbig)
      (Set.range (commonTimeInclusion timeLe)))

theorem restrictCommonTimeLp_compLpL
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (map : E →L[ℂ] F)
    (value : MeasureTheory.Lp E p (commonTimeMeasure Tbig)) :
    restrictCommonTimeLp timeLe
        ((map.compLpL p (commonTimeMeasure Tbig)) value) =
      (map.compLpL p (commonTimeMeasure Tsmall))
        (restrictCommonTimeLp timeLe value) := by
  apply MeasureTheory.Lp.ext
  have restrictedMapAE :=
    restrictCommonTimeLp_apply_ae timeLe
      ((map.compLpL p (commonTimeMeasure Tbig)) value)
  have restrictedValueAE :=
    restrictCommonTimeLp_apply_ae timeLe value
  have bigMapAE :=
    ae_comp_commonTimeInclusion timeLe
      (map.coeFn_compLpL value)
  have smallMapAE :=
    map.coeFn_compLpL (restrictCommonTimeLp timeLe value)
  filter_upwards [
    restrictedMapAE, restrictedValueAE, bigMapAE, smallMapAE] with
      time restrictedMapEq restrictedValueEq bigMapEq smallMapEq
  rw [restrictedMapEq, bigMapEq, smallMapEq, restrictedValueEq]

/--
The `L²` representative of a genuinely restricted continuous path is the
restriction of the original representative.
-/
theorem boundedContinuousFunction_toLp_compContinuous
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (path : BoundedContinuousFunction (Icc (0 : ℝ) Tbig) E) :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure Tsmall) ℂ
        (path.compContinuous (commonTimeInclusion timeLe)) =
      restrictCommonTimeLp timeLe
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure Tbig) ℂ path) := by
  apply MeasureTheory.Lp.ext
  have smallPathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure Tsmall)
      ℂ (path.compContinuous (commonTimeInclusion timeLe))
  have restrictedAE :=
    restrictCommonTimeLp_apply_ae timeLe
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure Tbig) ℂ path)
  have bigPathAE :=
    ae_comp_commonTimeInclusion timeLe
      (BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure Tbig)
        ℂ path)
  filter_upwards [smallPathAE, restrictedAE, bigPathAE] with
      time smallPathEq restrictedEq bigPathEq
  rw [smallPathEq, restrictedEq, bigPathEq]
  rfl

/-- Restriction commutes with the actual transverse-to-whole inclusion. -/
theorem restrictCommonTimeLp_transverseSpaceTimeInclusion
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (state : TransverseSpaceTimeState Tbig) :
    restrictCommonTimeLp timeLe
        (transverseSpaceTimeInclusion Tbig state) =
      transverseSpaceTimeInclusion Tsmall
        (restrictCommonTimeLp timeLe state) := by
  exact restrictCommonTimeLp_compLpL timeLe
    wholeTransverseVorticitySubmodule.subtypeL state

/-- Restriction commutes with evaluation at an actual Fourier wave. -/
theorem restrictCommonTimeLp_fixedWaveSpaceTimeRestriction
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (wave : IntegerWavevector)
    (state : SpaceTimeState Tbig) :
    restrictCommonTimeLp timeLe
        (fixedWaveSpaceTimeRestriction Tbig wave state) =
      fixedWaveSpaceTimeRestriction Tsmall wave
        (restrictCommonTimeLp timeLe state) := by
  exact restrictCommonTimeLp_compLpL timeLe
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave) state

/-- Restricting the physical interval cannot increase one wave's gradient mass. -/
theorem wholeSpaceTimeVorticityGradientDensity_restrict_le
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (state : SpaceTimeState Tbig)
    (wave : IntegerWavevector) :
    wholeSpaceTimeVorticityGradientDensity Tsmall
        (restrictCommonTimeLp timeLe state) wave ≤
      wholeSpaceTimeVorticityGradientDensity Tbig state wave := by
  unfold wholeSpaceTimeVorticityGradientDensity
  rw [← restrictCommonTimeLp_fixedWaveSpaceTimeRestriction
    timeLe wave state]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (restrictCommonTimeLp_norm_le timeLe
        (fixedWaveSpaceTimeRestriction Tbig wave state)))
    (integerWaveNormSq_nonneg wave)

/-- The whole gradient budget survives literal restriction of physical time. -/
theorem wholeSpaceTimeVorticityGradientDensity_restrict_summable
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (state : SpaceTimeState Tbig)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity Tbig state wave) :
    Summable fun wave : IntegerWavevector =>
      wholeSpaceTimeVorticityGradientDensity Tsmall
        (restrictCommonTimeLp timeLe state) wave :=
  gradientSummable.of_nonneg_of_le
    (fun wave =>
      wholeSpaceTimeVorticityGradientDensity_nonneg
        Tsmall (restrictCommonTimeLp timeLe state) wave)
    (wholeSpaceTimeVorticityGradientDensity_restrict_le timeLe state)

/-- The actual quadratic nonlinear row commutes with physical-time restriction. -/
theorem restrictCommonTimeLp_transverseSpaceTimeNonlinearRow
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (state : TransverseSpaceTimeState Tbig)
    (wave : IntegerWavevector) :
    restrictCommonTimeLp timeLe
        (transverseSpaceTimeNonlinearRow state wave) =
      transverseSpaceTimeNonlinearRow
        (restrictCommonTimeLp timeLe state) wave := by
  apply MeasureTheory.Lp.ext
  have restrictedRowAE :=
    restrictCommonTimeLp_apply_ae timeLe
      (transverseSpaceTimeNonlinearRow state wave)
  have bigRowAE :=
    ae_comp_commonTimeInclusion timeLe
      (transverseSpaceTimeNonlinearRow_coeFn state wave)
  have smallRowAE :=
    transverseSpaceTimeNonlinearRow_coeFn
      (restrictCommonTimeLp timeLe state) wave
  have restrictedStateAE :=
    restrictCommonTimeLp_apply_ae timeLe state
  filter_upwards [
    restrictedRowAE, bigRowAE, smallRowAE, restrictedStateAE] with
      time restrictedRowEq bigRowEq smallRowEq restrictedStateEq
  rw [restrictedRowEq, bigRowEq, smallRowEq]
  simp only [transverseSpaceTimeNonlinearRowFunction]
  rw [restrictedStateEq]

private theorem wholeSpaceTimeNonlinearNegativeOneFunction_restrict_ae
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (state : TransverseSpaceTimeState Tbig) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      wholeSpaceTimeNonlinearNegativeOneFunction
          (restrictCommonTimeLp timeLe state) time =
        wholeSpaceTimeNonlinearNegativeOneFunction state
          (commonTimeInclusion timeLe time) := by
  filter_upwards [
    restrictCommonTimeLp_apply_ae timeLe state] with
      time restrictedStateEq
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
      ((restrictCommonTimeLp timeLe state) time) =
    nonlinearAt (state (commonTimeInclusion timeLe time))
  exact congrArg nonlinearAt restrictedStateEq

private theorem wholeSpaceTimeViscousNegativeOneFunction_restrict_ae
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (ν : ℝ)
    (state : SpaceTimeState Tbig) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      wholeSpaceTimeViscousNegativeOneFunction ν
          (restrictCommonTimeLp timeLe state) time =
        wholeSpaceTimeViscousNegativeOneFunction ν state
          (commonTimeInclusion timeLe time) := by
  filter_upwards [
    restrictCommonTimeLp_apply_ae timeLe state] with
      time restrictedStateEq
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
            ν point gradientSummable
        else 0
  change viscousAt
      ((restrictCommonTimeLp timeLe state) time) =
    viscousAt (state (commonTimeInclusion timeLe time))
  exact congrArg viscousAt restrictedStateEq

/--
An integral over a causal prefix of the shorter interval is literally the
same integral over that prefix in the larger interval.  The target measure
is first restricted to the actual image; the causal prefix lies wholly in
that image, so no mass is added or discarded.
-/
theorem commonTime_setIntegral_Iic_inclusion
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (time : Icc (0 : ℝ) Tsmall)
    (function : Icc (0 : ℝ) Tbig → E) :
    (∫ earlier in Iic time,
        function (commonTimeInclusion timeLe earlier)
        ∂(commonTimeMeasure Tsmall)) =
      ∫ earlier in Iic (commonTimeInclusion timeLe time),
        function earlier
        ∂(commonTimeMeasure Tbig) := by
  have preimageEq :
      commonTimeInclusion timeLe ⁻¹'
          Iic (commonTimeInclusion timeLe time) =
        Iic time := by
    ext earlier
    rfl
  have causalSubset :
      Iic (commonTimeInclusion timeLe time) ⊆
        Set.range (commonTimeInclusion timeLe) := by
    intro earlier earlierMem
    let shortEarlier : Icc (0 : ℝ) Tsmall :=
      ⟨earlier.1,
        ⟨earlier.2.1,
          earlierMem.trans time.2.2⟩⟩
    exact ⟨shortEarlier, Subtype.ext rfl⟩
  have transported :=
    (commonTimeInclusion_measurePreserving timeLe)
      |>.setIntegral_preimage_emb
        (commonTimeInclusion_measurableEmbedding timeLe)
        function
        (Iic (commonTimeInclusion timeLe time))
  rw [preimageEq] at transported
  rw [Measure.restrict_restrict_of_subset causalSubset] at transported
  exact transported

/--
The causal heat/Duhamel value is horizon-independent on a literal common
physical prefix.
-/
theorem fixedWaveHeatDuhamelValue_restrict
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    (ν : ℝ)
    (state : TransverseSpaceTimeState Tbig)
    (wave : IntegerWavevector)
    (initial : ComplexCoordinateVector)
    (time : Icc (0 : ℝ) Tsmall) :
    fixedWaveHeatDuhamelValue Tsmall ν wave initial
        (transverseSpaceTimeNonlinearRow
          (restrictCommonTimeLp timeLe state) wave) time =
      fixedWaveHeatDuhamelValue Tbig ν wave initial
        (transverseSpaceTimeNonlinearRow state wave)
        (commonTimeInclusion timeLe time) := by
  let bigRow :=
    transverseSpaceTimeNonlinearRow state wave
  let smallRow :=
    transverseSpaceTimeNonlinearRow
      (restrictCommonTimeLp timeLe state) wave
  have rowAE :
      ∀ᵐ earlier ∂(commonTimeMeasure Tsmall),
        smallRow earlier =
          bigRow (commonTimeInclusion timeLe earlier) := by
    have restrictedAE :=
      restrictCommonTimeLp_apply_ae timeLe bigRow
    rw [restrictCommonTimeLp_transverseSpaceTimeNonlinearRow
      timeLe state wave] at restrictedAE
    exact restrictedAE
  have integralCongr :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            smallRow earlier
          ∂(commonTimeMeasure Tsmall)) =
        ∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            bigRow (commonTimeInclusion timeLe earlier)
          ∂(commonTimeMeasure Tsmall) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [
      MeasureTheory.ae_restrict_le rowAE] with
        earlier rowEq
    rw [rowEq]
  have integralTransport :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            bigRow (commonTimeInclusion timeLe earlier)
          ∂(commonTimeMeasure Tsmall)) =
        ∫ earlier in Iic (commonTimeInclusion timeLe time),
          finiteStateVorticityHeatMultiplier
              ν ((commonTimeInclusion timeLe time).1 - earlier.1)
              wave •
            bigRow earlier
          ∂(commonTimeMeasure Tbig) := by
    simpa only [commonTimeInclusion_apply] using
      commonTime_setIntegral_Iic_inclusion timeLe time
        (fun earlier =>
          finiteStateVorticityHeatMultiplier
              ν ((commonTimeInclusion timeLe time).1 - earlier.1)
              wave •
            bigRow earlier)
  unfold fixedWaveHeatDuhamelValue
  rw [integralCongr, integralTransport]
  rfl

/--
The target-side receipt carried by a longer unforced whole path restricts
to every positive shorter physical horizon.
-/
noncomputable def restrictWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {Tsmall Tbig : ℝ}
    (smallTimePos : 0 < Tsmall)
    (timeLe : Tsmall ≤ Tbig)
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState Tbig) :
    WholeContinuousMildSerrinReceipt
      ν initialState Tsmall := by
  let restrictedState : SpaceTimeState Tsmall :=
    restrictCommonTimeLp timeLe receipt.stateLimit
  let restrictedTransverse : TransverseSpaceTimeState Tsmall :=
    restrictCommonTimeLp timeLe receipt.transverseLimit
  let restrictedTangent : SpaceTimeState Tsmall :=
    restrictCommonTimeLp timeLe receipt.wholeTangent
  let restrictedPath :
      BoundedContinuousFunction
        (Icc (0 : ℝ) Tsmall)
        ComplexVorticityHilbertState :=
    receipt.wholePath.compContinuous
      (commonTimeInclusion timeLe)
  refine
    { requestedTimePos := smallTimePos
      stateLimit := restrictedState
      transverseLimit := restrictedTransverse
      stateLimit_eq_transverse := ?_
      wholePath := restrictedPath
      wholePath_toLp_eq_stateLimit := ?_
      wholePath_initial := ?_
      wholePath_zero_row := ?_
      transverse_fourierReality_ae := ?_
      gradient_summable := ?_
      wholeTangent := restrictedTangent
      wholeTangent_eq_unforced_ae := ?_
      rowExtension := receipt.rowExtension
      rowExtension_on_interval := ?_
      rowTangent := fun wave waveNe time =>
        receipt.rowTangent wave waveNe
          (commonTimeInclusion timeLe time)
      rowTangent_eq_unforced_ae := ?_
      rowTangent_eq_wholeTangent_ae := ?_
      rowExtension_absolutelyContinuous := ?_
      rowExtension_ae_hasDerivAt := ?_
      row_mild_identity := ?_ }
  · dsimp only [restrictedState, restrictedTransverse]
    rw [← restrictCommonTimeLp_transverseSpaceTimeInclusion]
    exact congrArg (restrictCommonTimeLp timeLe)
      receipt.stateLimit_eq_transverse
  · dsimp only [restrictedPath, restrictedState]
    rw [boundedContinuousFunction_toLp_compContinuous,
      receipt.wholePath_toLp_eq_stateLimit]
  · dsimp only [restrictedPath]
    exact receipt.wholePath_initial
  · intro time
    dsimp only [restrictedPath]
    exact receipt.wholePath_zero_row
      (commonTimeInclusion timeLe time)
  · have bigReality :=
      ae_comp_commonTimeInclusion timeLe
        receipt.transverse_fourierReality_ae
    have restrictedTransverseAE :=
      restrictCommonTimeLp_apply_ae timeLe
        receipt.transverseLimit
    filter_upwards [
      bigReality, restrictedTransverseAE] with
        time reality restrictedEq
    dsimp only [restrictedTransverse]
    rw [restrictedEq]
    exact reality
  · exact wholeSpaceTimeVorticityGradientDensity_restrict_summable
      timeLe receipt.stateLimit receipt.gradient_summable
  · have restrictedTangentAE :=
      restrictCommonTimeLp_apply_ae timeLe receipt.wholeTangent
    have bigEquation :=
      ae_comp_commonTimeInclusion timeLe
        receipt.wholeTangent_eq_unforced_ae
    have nonlinearAE :=
      wholeSpaceTimeNonlinearNegativeOneFunction_restrict_ae
        timeLe receipt.transverseLimit
    have viscousAE :=
      wholeSpaceTimeViscousNegativeOneFunction_restrict_ae
        timeLe ν.coeff receipt.stateLimit
    filter_upwards [
      restrictedTangentAE, bigEquation, nonlinearAE, viscousAE] with
        time restrictedTangentEq bigEq nonlinearEq viscousEq
    dsimp only [
      restrictedTangent, restrictedTransverse, restrictedState]
    rw [restrictedTangentEq, bigEq, nonlinearEq, viscousEq]
  · intro wave waveNe time
    dsimp only [restrictedPath]
    exact receipt.rowExtension_on_interval
      wave waveNe (commonTimeInclusion timeLe time)
  · intro wave waveNe
    have bigEquation :=
      ae_comp_commonTimeInclusion timeLe
        (receipt.rowTangent_eq_unforced_ae wave waveNe)
    have restrictedTransverseAE :=
      restrictCommonTimeLp_apply_ae timeLe
        receipt.transverseLimit
    filter_upwards [
      bigEquation, restrictedTransverseAE] with
        time bigEq restrictedTransverseEq
    dsimp only [restrictedTransverse, restrictedPath]
    rw [bigEq, restrictedTransverseEq]
    rfl
  · intro wave waveNe
    have bigEquation :=
      ae_comp_commonTimeInclusion timeLe
        (receipt.rowTangent_eq_wholeTangent_ae wave waveNe)
    have restrictedTangentAE :=
      restrictCommonTimeLp_apply_ae timeLe receipt.wholeTangent
    filter_upwards [
      bigEquation, restrictedTangentAE] with
        time bigEq restrictedTangentEq
    dsimp only [restrictedTangent]
    rw [restrictedTangentEq, bigEq]
  · intro wave waveNe
    apply (receipt.rowExtension_absolutelyContinuous wave waveNe).mono
    rw [uIcc_of_le smallTimePos.le,
      uIcc_of_le receipt.requestedTimePos.le]
    exact Icc_subset_Icc le_rfl timeLe
  · intro wave waveNe
    filter_upwards [
      receipt.rowExtension_ae_hasDerivAt wave waveNe] with
        actual bigDerivative
    intro actualMem
    have actualMemSmall :
        actual ∈ Icc (0 : ℝ) Tsmall := by
      simpa only [uIcc_of_le smallTimePos.le] using actualMem
    have actualMemBig :
        actual ∈ Icc (0 : ℝ) Tbig :=
      ⟨actualMemSmall.1, actualMemSmall.2.trans timeLe⟩
    have applied :=
      bigDerivative
        (by
          simpa only [
            uIcc_of_le receipt.requestedTimePos.le] using
              actualMemBig)
    convert applied using 1
    rw [commonTimeZeroExtension_of_mem
        Tsmall _ actual actualMemSmall,
      commonTimeZeroExtension_of_mem
        Tbig _ actual actualMemBig]
    rfl
  · intro wave waveNe time
    dsimp only [restrictedPath, restrictedTransverse]
    calc
      receipt.wholePath
            (commonTimeInclusion timeLe time) wave =
          fixedWaveHeatDuhamelValue Tbig ν.coeff wave
            (initialState wave)
            (transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave)
            (commonTimeInclusion timeLe time) :=
        receipt.row_mild_identity wave waveNe
          (commonTimeInclusion timeLe time)
      _ =
          fixedWaveHeatDuhamelValue Tsmall ν.coeff wave
            (initialState wave)
            (transverseSpaceTimeNonlinearRow
              (restrictCommonTimeLp timeLe
                receipt.transverseLimit) wave) time :=
        (fixedWaveHeatDuhamelValue_restrict
          timeLe ν.coeff receipt.transverseLimit wave
          (initialState wave) time).symm

/--
Two actual unforced whole mild/Serrin receipts with the same initial state
are the same path on their common physical horizon.

No overlap certificate, restart choice, cutoff, payment bound, or target
equality is accepted by the theorem mouth.
-/
theorem wholeContinuousMildSerrin_overlap
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {Tsmall Tbig : ℝ}
    (small :
      WholeContinuousMildSerrinReceipt
        ν initialState Tsmall)
    (big :
      WholeContinuousMildSerrinReceipt
        ν initialState Tbig)
    (timeLe : Tsmall ≤ Tbig) :
    small.wholePath =
      big.wholePath.compContinuous
        (commonTimeInclusion timeLe) := by
  let restricted :=
    restrictWholeContinuousMildSerrinReceipt
      small.requestedTimePos timeLe big
  have samePath :=
    wholeContinuousMildSerrin_sameInitial_unique
      small restricted
  simpa only [
    restricted,
    restrictWholeContinuousMildSerrinReceipt] using samePath

end

end ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
end NavierStokes
end SaturationMonoid
