import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Set
import H0mework.NavierStokes.GeneratedPaths.FiniteObservedCompactness

/-!
# Strong space-time compactness of the generated critical path family

For every positive finite time interval, this module places every actual
source-generated critical Galerkin trajectory in the common whole Fourier
carrier

`L²([0,T]; ℓ²(ℤ³; ℂ³))`

and proves that the closure of the complete generated family is compact.
The proof combines two source-owned analytic facts already generated on the
same path:

* compactness of every fixed finite Fourier observation; and
* the cutoff-independent high-frequency tail budget.

For an arbitrary accuracy, a finite frequency cube is chosen after the
family is formed.  The sharp projection of every member lies in one compact
finite-observation image, while the actual tail budget places the full
trajectory uniformly close to that image.  Finite half-radius covers then
give total boundedness of the whole family.

No subsequence, compactness witness, support-coverage hypothesis, target
limit, or high-frequency silence is stored in `GeneratedCriticalScalePath`.
This is a downstream PDE compactness consumer.  It proves strong whole-carrier
space-time relative compactness; passage through the Navier--Stokes nonlinear
term remains a separate consumer.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness

open scoped ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalHighFrequencyTail
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness

noncomputable section

abbrev commonTimeMeasure (requestedTime : ℝ) :
    Measure (Icc (0 : ℝ) requestedTime) :=
  Measure.comap
    (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
    (volume.restrict (Icc (0 : ℝ) requestedTime))

abbrev SpaceTimeState (requestedTime : ℝ) :=
  ↥(MeasureTheory.Lp ComplexVorticityHilbertState 2
    (commonTimeMeasure requestedTime))

def lowFrequencyCube (radius : ℕ) : Finset IntegerWavevector :=
  Fintype.piFinset fun _ : Coordinate =>
    Finset.Icc (-(radius : ℤ)) (radius : ℤ)

theorem lowFrequencyCube_outside_normSq_gt
    (radius : ℕ)
    (wave : IntegerWavevector)
    (outside : wave ∉ lowFrequencyCube radius) :
    (radius : ℝ) ^ 2 < integerWaveNormSq wave := by
  by_contra notGreater
  have normLe :
      integerWaveNormSq wave ≤ (radius : ℝ) ^ 2 :=
    le_of_not_gt notGreater
  have shellLe :
      integerWaveShellSq wave ≤ (radius : ℤ) ^ 2 := by
    rw [integerWaveNormSq_eq_integerWaveShellSq] at normLe
    exact_mod_cast normLe
  apply outside
  rw [lowFrequencyCube, Fintype.mem_piFinset]
  intro coordinate
  rw [Finset.mem_Icc]
  have coordinateSqLe :
      wave coordinate ^ 2 ≤ integerWaveShellSq wave := by
    unfold integerWaveShellSq
    exact Finset.single_le_sum
      (fun index _ => sq_nonneg (wave index))
      (Finset.mem_univ coordinate)
  have coordinateSqLeRadius :
      wave coordinate ^ 2 ≤ (radius : ℤ) ^ 2 :=
    coordinateSqLe.trans shellLe
  constructor <;> nlinarith [sq_nonneg (wave coordinate)]

def finiteObservedEmbedding
    (observed : Finset IntegerWavevector) :
    FiniteObservedCoefficientState observed →L[ℂ]
      ComplexVorticityHilbertState :=
  ∑ wave : {wave : IntegerWavevector // wave ∈ observed},
    (lp.singleContinuousLinearMap ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave.1).comp
      (ContinuousLinearMap.proj wave)

def finiteObservedRestriction
    (observed : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℂ]
      FiniteObservedCoefficientState observed :=
  ContinuousLinearMap.pi fun wave =>
    lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave.1

@[simp] theorem finiteObservedRestriction_apply
    (observed : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : {wave : IntegerWavevector // wave ∈ observed}) :
    finiteObservedRestriction observed state wave =
      state wave.1 :=
  rfl

def sharpSupportProjectionCLM
    (observed : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℂ]
      ComplexVorticityHilbertState :=
  (finiteObservedEmbedding observed).comp
    (finiteObservedRestriction observed)

@[simp] theorem finiteObservedEmbedding_apply
    (observed : Finset IntegerWavevector)
    (state : FiniteObservedCoefficientState observed)
    (wave : IntegerWavevector) :
    finiteObservedEmbedding observed state wave =
      if waveMem : wave ∈ observed
      then state ⟨wave, waveMem⟩
      else 0 := by
  classical
  simp only [finiteObservedEmbedding, sum_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,
    lp.singleContinuousLinearMap_apply, lp.coeFn_sum,
    Finset.sum_apply]
  by_cases waveMem : wave ∈ observed
  · rw [dif_pos waveMem]
    rw [Finset.sum_eq_single ⟨wave, waveMem⟩]
    · simp
    · intro later laterMem laterNe
      have valueNe : later.1 ≠ wave := by
        intro valueEq
        apply laterNe
        exact Subtype.ext valueEq
      exact lp.single_apply_ne
        (E := fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 later.1 (state later) valueNe.symm
    · simp
  · rw [dif_neg waveMem]
    apply Finset.sum_eq_zero
    intro later laterMem
    have laterNe : later.1 ≠ wave := by
      intro laterEq
      subst wave
      exact waveMem later.2
    exact lp.single_apply_ne
      (E := fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 later.1 (state later) laterNe.symm

noncomputable def observedPathToSpaceTime
    (requestedTime : ℝ)
    (observed : Finset IntegerWavevector) :
    BoundedContinuousFunction
        (Icc (0 : ℝ) requestedTime)
        (FiniteObservedCoefficientState observed) →L[ℂ]
      SpaceTimeState requestedTime :=
  (BoundedContinuousFunction.toLp 2
      (commonTimeMeasure requestedTime) ℂ).comp
    ((finiteObservedEmbedding observed).compLeftContinuousBounded
      (Icc (0 : ℝ) requestedTime))

def generatedWholeTrajectory
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexVorticityHilbertState :=
  (path.commonTimeBudget
    θLtOne requestedTimePos).trajectory time.1

theorem generatedWholeTrajectory_continuous
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ) :
    Continuous
      (generatedWholeTrajectory
        θLtOne requestedTimePos path) := by
  rw [continuous_iff_continuousAt]
  intro time
  have evolves :=
    ((path.commonTimeBudget θLtOne requestedTimePos).physicalProperties
      time.1 time.2).1
  exact evolves.continuousAt.comp continuousAt_subtype_val

def generatedWholeBoundedPath
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨generatedWholeTrajectory θLtOne requestedTimePos path,
      generatedWholeTrajectory_continuous
        θLtOne requestedTimePos path⟩

def generatedCriticalSpaceTimePath
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ) :
    SpaceTimeState requestedTime :=
  BoundedContinuousFunction.toLp 2
    (commonTimeMeasure requestedTime) ℂ
    (generatedWholeBoundedPath
      θLtOne requestedTimePos path)

def generatedCriticalSpaceTimePathFamily
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime) :
    Set (SpaceTimeState requestedTime) :=
  Set.range fun path : GeneratedCriticalScalePath ν θ =>
    generatedCriticalSpaceTimePath
      θLtOne requestedTimePos path

theorem finiteObservedEmbedding_finiteObservedCoefficientState
    (observed : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteObservedEmbedding observed
        (finiteObservedCoefficientState observed state) =
      complexSharpSupportProjection observed state := by
  ext wave
  by_cases waveMem : wave ∈ observed
  · simp [finiteObservedCoefficientState, waveMem]
  · simp [waveMem]

theorem sharpSupportProjectionCLM_apply
    (observed : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    sharpSupportProjectionCLM observed state =
      complexSharpSupportProjection observed state := by
  exact
    finiteObservedEmbedding_finiteObservedCoefficientState
      observed state

def projectedGeneratedCriticalSpaceTimePath
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (observed : Finset IntegerWavevector)
    (path : GeneratedCriticalScalePath ν θ) :
    SpaceTimeState requestedTime :=
  observedPathToSpaceTime requestedTime observed
    (generatedFiniteObservedBoundedPath
      θLtOne requestedTimePos observed path)

def compactObservedSpaceTimeSet
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (observed : Finset IntegerWavevector) :
    Set (SpaceTimeState requestedTime) :=
  observedPathToSpaceTime requestedTime observed ''
    closure
      (generatedFiniteObservedPathFamily
        (ν := ν) θLtOne requestedTimePos observed)

theorem compactObservedSpaceTimeSet_isCompact
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (observed : Finset IntegerWavevector) :
    IsCompact
      (compactObservedSpaceTimeSet
        (ν := ν) θLtOne requestedTimePos observed) := by
  exact
    (generatedFiniteObservedPathFamily_isCompact_closure
      (ν := ν) θLtOne requestedTimePos observed).image
      (observedPathToSpaceTime
        requestedTime observed).continuous

theorem projectedGeneratedCriticalSpaceTimePath_mem_compactObserved
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (observed : Finset IntegerWavevector)
    (path : GeneratedCriticalScalePath ν θ) :
    projectedGeneratedCriticalSpaceTimePath
        θLtOne requestedTimePos observed path ∈
      compactObservedSpaceTimeSet
        (ν := ν) θLtOne requestedTimePos observed := by
  unfold projectedGeneratedCriticalSpaceTimePath
    compactObservedSpaceTimeSet
  refine ⟨generatedFiniteObservedBoundedPath
      θLtOne requestedTimePos observed path, ?_, rfl⟩
  exact subset_closure ⟨path, rfl⟩

theorem norm_sub_lowFrequencyCubeProjection_sq_le_tail
    (radius : ℕ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0) :
    ‖state -
        complexSharpSupportProjection
          (lowFrequencyCube radius) state‖ ^ 2 ≤
      finiteStateVorticityHighFrequencyTailMass modes
        ((radius : ℝ) ^ 2) state := by
  have normIdentity :
      ‖state -
          complexSharpSupportProjection
            (lowFrequencyCube radius) state‖ ^ 2 =
        ∑' wave,
          ‖(state -
              complexSharpSupportProjection
                (lowFrequencyCube radius) state) wave‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (state -
          complexSharpSupportProjection
            (lowFrequencyCube radius) state))
  rw [normIdentity]
  rw [tsum_eq_sum
    (s := modes.filter fun wave =>
      (radius : ℝ) ^ 2 < integerWaveNormSq wave)]
  · unfold finiteStateVorticityHighFrequencyTailMass
    apply Finset.sum_le_sum
    intro wave waveMem
    by_cases retained : wave ∈ lowFrequencyCube radius
    · simpa [complexSharpSupportProjection_apply, retained] using
        (complexCoordinateAmplitudeSq_nonneg (state wave))
    · have projectionZero :
          complexSharpSupportProjection
              (lowFrequencyCube radius) state wave =
            0 := by
        simp [complexSharpSupportProjection_apply, retained]
      rw [show
        (state -
            complexSharpSupportProjection
              (lowFrequencyCube radius) state) wave =
          state wave by
            exact sub_eq_self.mpr projectionZero]
      exact complexCoordinateVector_norm_sq_le_amplitudeSq
        (state wave)
  · intro wave waveNotMem
    by_cases modeMem : wave ∈ modes
    · have notHigh :
          ¬((radius : ℝ) ^ 2 < integerWaveNormSq wave) := by
        intro high
        exact waveNotMem (Finset.mem_filter.mpr ⟨modeMem, high⟩)
      have retained : wave ∈ lowFrequencyCube radius := by
        by_contra outside
        exact notHigh
          (lowFrequencyCube_outside_normSq_gt radius wave outside)
      simp [complexSharpSupportProjection_apply, retained]
    · have stateZero : state wave = 0 :=
        supported wave modeMem
      simp [complexSharpSupportProjection_apply, stateZero]

theorem spaceTime_norm_sq_eq_integral
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    ‖state‖ ^ 2 =
      ∫ time,
        ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) := by
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  norm_num
  have powerIdentity :
      ((∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime)) ^
            ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  convert powerIdentity using 1
  all_goals norm_num

theorem generatedSpaceTime_sub_projection_coeFn_ae
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (observed : Finset IntegerWavevector)
    (path : GeneratedCriticalScalePath ν θ) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path -
        projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos observed path) time =
        generatedWholeTrajectory
            θLtOne requestedTimePos path time -
          complexSharpSupportProjection observed
            (generatedWholeTrajectory
              θLtOne requestedTimePos path time) := by
  have wholeAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (generatedWholeBoundedPath
        θLtOne requestedTimePos path)
  have projectionAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      ((finiteObservedEmbedding observed).compLeftContinuousBounded
        (Icc (0 : ℝ) requestedTime)
        (generatedFiniteObservedBoundedPath
          θLtOne requestedTimePos observed path))
  have subAE :=
    MeasureTheory.Lp.coeFn_sub
      (generatedCriticalSpaceTimePath
        θLtOne requestedTimePos path)
      (projectedGeneratedCriticalSpaceTimePath
        θLtOne requestedTimePos observed path)
  filter_upwards [subAE, wholeAE, projectionAE] with
    time subEq wholeEq projectionEq
  rw [subEq]
  change
    (generatedCriticalSpaceTimePath
        θLtOne requestedTimePos path) time -
        (projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos observed path) time =
      _
  change
    ((BoundedContinuousFunction.toLp 2
      (commonTimeMeasure requestedTime) ℂ)
      (generatedWholeBoundedPath
        θLtOne requestedTimePos path)) time -
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ)
          ((finiteObservedEmbedding observed).compLeftContinuousBounded
            (Icc (0 : ℝ) requestedTime)
            (generatedFiniteObservedBoundedPath
              θLtOne requestedTimePos observed path))) time =
      _
  rw [wholeEq, projectionEq]
  change
    generatedWholeTrajectory θLtOne requestedTimePos path time -
        finiteObservedEmbedding observed
          (finiteObservedCoefficientState observed
            (generatedWholeTrajectory
              θLtOne requestedTimePos path time)) =
      _
  rw [finiteObservedEmbedding_finiteObservedCoefficientState]

theorem commonTime_integral_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (function : ℝ → ℝ) :
    (∫ time : Icc (0 : ℝ) requestedTime,
        function time.1 ∂(commonTimeMeasure requestedTime)) =
      ∫ time in (0 : ℝ)..requestedTime, function time := by
  rw [MeasureTheory.integral_subtype_comap measurableSet_Icc]
  rw [intervalIntegral.integral_of_le requestedTimeNonneg]
  rw [Measure.restrict_restrict_of_subset Subset.rfl]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

theorem generatedSpaceTime_projection_norm_sq_eq_intervalIntegral
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (observed : Finset IntegerWavevector)
    (path : GeneratedCriticalScalePath ν θ) :
    ‖generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path -
        projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos observed path‖ ^ 2 =
      ∫ time in (0 : ℝ)..requestedTime,
        ‖(path.commonTimeBudget
              θLtOne requestedTimePos).trajectory time -
            complexSharpSupportProjection observed
              ((path.commonTimeBudget
                θLtOne requestedTimePos).trajectory time)‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  calc
    (∫ time,
        ‖(generatedCriticalSpaceTimePath
              θLtOne requestedTimePos path -
            projectedGeneratedCriticalSpaceTimePath
              θLtOne requestedTimePos observed path) time‖ ^ 2
          ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          ‖generatedWholeTrajectory
                θLtOne requestedTimePos path time -
              complexSharpSupportProjection observed
                (generatedWholeTrajectory
                  θLtOne requestedTimePos path time)‖ ^ 2
            ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [
        generatedSpaceTime_sub_projection_coeFn_ae
          θLtOne requestedTimePos observed path] with time pointwiseEq
      rw [pointwiseEq]
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          ‖(path.commonTimeBudget
                θLtOne requestedTimePos).trajectory time -
              complexSharpSupportProjection observed
                ((path.commonTimeBudget
                  θLtOne requestedTimePos).trajectory time)‖ ^ 2 := by
      simpa [generatedWholeTrajectory] using
        (commonTime_integral_eq_intervalIntegral
          requestedTime requestedTimePos.le
          (fun time =>
            ‖(path.commonTimeBudget
                  θLtOne requestedTimePos).trajectory time -
                complexSharpSupportProjection observed
                  ((path.commonTimeBudget
                    θLtOne requestedTimePos).trajectory time)‖ ^ 2))

theorem generatedSpaceTime_projection_norm_sq_le_tail_integral
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ)
    (path : GeneratedCriticalScalePath ν θ) :
    ‖generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path -
        projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos
          (lowFrequencyCube radius) path‖ ^ 2 ≤
      ∫ time in (0 : ℝ)..requestedTime,
        finiteStateVorticityHighFrequencyTailMass
          (generatedSupport path.current)
          ((radius : ℝ) ^ 2)
          ((path.commonTimeBudget
            θLtOne requestedTimePos).trajectory time) := by
  rw [generatedSpaceTime_projection_norm_sq_eq_intervalIntegral]
  simp_rw [← sharpSupportProjectionCLM_apply]
  let trajectory : ℝ → ComplexVorticityHilbertState :=
    (path.commonTimeBudget θLtOne requestedTimePos).trajectory
  let modes : Finset IntegerWavevector :=
    generatedSupport path.current
  have trajectoryContinuousOn :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime) := by
    intro time timeMem
    exact
      ((path.commonTimeBudget
          θLtOne requestedTimePos).physicalProperties
        time timeMem).1.continuousAt.continuousWithinAt
  have projectionContinuousOn :
      ContinuousOn
        (fun time =>
          sharpSupportProjectionCLM
            (lowFrequencyCube radius) (trajectory time))
        (Icc (0 : ℝ) requestedTime) := by
    change
      ContinuousOn
        ((sharpSupportProjectionCLM
          (lowFrequencyCube radius)) ∘ trajectory)
        (Icc (0 : ℝ) requestedTime)
    exact
      (sharpSupportProjectionCLM
          (lowFrequencyCube radius)).continuous.comp_continuousOn
        trajectoryContinuousOn
  have differenceContinuousOn :
      ContinuousOn
        (fun time =>
          ‖trajectory time -
              sharpSupportProjectionCLM
                (lowFrequencyCube radius) (trajectory time)‖ ^ 2)
        (Icc (0 : ℝ) requestedTime) := by
    change
      ContinuousOn
        ((fun time =>
          ‖trajectory time -
              sharpSupportProjectionCLM
                (lowFrequencyCube radius) (trajectory time)‖) ^ 2)
        (Icc (0 : ℝ) requestedTime)
    exact
      (trajectoryContinuousOn.sub projectionContinuousOn).norm.pow 2
  have differenceIntegral :
      IntervalIntegrable
        (fun time =>
          ‖trajectory time -
              sharpSupportProjectionCLM
                (lowFrequencyCube radius) (trajectory time)‖ ^ 2)
        volume 0 requestedTime :=
    by
      rw [← uIcc_of_le requestedTimePos.le] at differenceContinuousOn
      exact differenceContinuousOn.intervalIntegrable
  have tailIntegral :
      IntervalIntegrable
        (fun time =>
          finiteStateVorticityHighFrequencyTailMass
            modes ((radius : ℝ) ^ 2) (trajectory time))
        volume 0 requestedTime := by
    apply ContinuousOn.intervalIntegrable
    intro time timeMem
    have timeMemIcc : time ∈ Icc (0 : ℝ) requestedTime := by
      simpa only [uIcc_of_le requestedTimePos.le] using timeMem
    exact
      (finiteStateVorticityHighFrequencyTailMass_continuousAt_of_hasDerivAt
        modes ((radius : ℝ) ^ 2) trajectory time
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory time))
        ((path.commonTimeBudget
          θLtOne requestedTimePos).physicalProperties
            time timeMemIcc).1).continuousWithinAt
  apply intervalIntegral.integral_mono_on
    requestedTimePos.le differenceIntegral tailIntegral
  intro time timeMem
  simpa only [sharpSupportProjectionCLM_apply] using
    norm_sub_lowFrequencyCubeProjection_sq_le_tail
      radius modes (trajectory time)
      (fun wave waveNotMem =>
        ((path.commonTimeBudget
          θLtOne requestedTimePos).physicalProperties
            time timeMem).2.1 wave waveNotMem)

theorem generatedSpaceTime_projection_norm_sq_le_uniformTail
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ)
    (radiusPos : 0 < radius)
    (path : GeneratedCriticalScalePath ν θ) :
    ‖generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path -
        projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos
          (lowFrequencyCube radius) path‖ ^ 2 ≤
      ((1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling ν θ) /
        (criticalEnstrophyAbsorptionCoefficient θ ν *
          (radius : ℝ) ^ 2) := by
  have thresholdPos : 0 < (radius : ℝ) ^ 2 := by
    positivity
  have denominatorNonneg :
      0 ≤
        criticalEnstrophyAbsorptionCoefficient θ ν *
          (radius : ℝ) ^ 2 := by
    exact mul_nonneg
      (criticalEnstrophyAbsorptionCoefficient_pos
        θ θLtOne ν).le
      thresholdPos.le
  have initialHalfLe :
      finiteStateVorticityHalfEnstrophy
          (generatedSupport path.current)
          ((path.commonTimeBudget
            θLtOne requestedTimePos).trajectory 0) ≤
        (1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling ν θ := by
    unfold finiteStateVorticityHalfEnstrophy
    apply mul_le_mul_of_nonneg_left
    · rw [(path.commonTimeBudget
        θLtOne requestedTimePos).initial]
      exact path.initialEnstrophy_le_ceiling
    · norm_num
  calc
    ‖generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path -
        projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos
          (lowFrequencyCube radius) path‖ ^ 2 ≤
      ∫ time in (0 : ℝ)..requestedTime,
        finiteStateVorticityHighFrequencyTailMass
          (generatedSupport path.current)
          ((radius : ℝ) ^ 2)
          ((path.commonTimeBudget
            θLtOne requestedTimePos).trajectory time) :=
      generatedSpaceTime_projection_norm_sq_le_tail_integral
        θLtOne requestedTimePos radius path
    _ ≤
        finiteStateVorticityHalfEnstrophy
              (generatedSupport path.current)
              ((path.commonTimeBudget
                θLtOne requestedTimePos).trajectory 0) /
          (criticalEnstrophyAbsorptionCoefficient θ ν *
            (radius : ℝ) ^ 2) :=
      (path.commonTimeBudget
        θLtOne requestedTimePos).highFrequencyTail
          ((radius : ℝ) ^ 2) thresholdPos
    _ ≤
        ((1 / 2 : ℝ) *
            criticalCoefficientEnstrophyCeiling ν θ) /
          (criticalEnstrophyAbsorptionCoefficient θ ν *
            (radius : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right initialHalfLe denominatorNonneg

theorem exists_lowFrequencyCube_uniformly_close
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (ε : ℝ)
    (εPos : 0 < ε) :
    ∃ radius : ℕ, 0 < radius ∧
      ∀ path : GeneratedCriticalScalePath ν θ,
        dist
            (generatedCriticalSpaceTimePath
              θLtOne requestedTimePos path)
            (projectedGeneratedCriticalSpaceTimePath
              θLtOne requestedTimePos
              (lowFrequencyCube radius) path) <
          ε := by
  let numerator : ℝ :=
    (1 / 2 : ℝ) *
      criticalCoefficientEnstrophyCeiling ν θ
  let absorption : ℝ :=
    criticalEnstrophyAbsorptionCoefficient θ ν
  have numeratorNonneg : 0 ≤ numerator := by
    exact mul_nonneg (by norm_num)
      (criticalCoefficientEnstrophyCeiling_nonneg ν θ)
  have absorptionPos : 0 < absorption := by
    exact criticalEnstrophyAbsorptionCoefficient_pos
      θ θLtOne ν
  have εSqPos : 0 < ε ^ 2 := sq_pos_of_pos εPos
  obtain ⟨radius, radiusGt⟩ :=
    exists_nat_gt (numerator / (absorption * ε ^ 2))
  have ratioNonneg :
      0 ≤ numerator / (absorption * ε ^ 2) :=
    div_nonneg numeratorNonneg
      (mul_nonneg absorptionPos.le εSqPos.le)
  have radiusRealPos : 0 < (radius : ℝ) :=
    ratioNonneg.trans_lt radiusGt
  have radiusPos : 0 < radius := by
    exact_mod_cast radiusRealPos
  have radiusLeSquare :
      (radius : ℝ) ≤ (radius : ℝ) ^ 2 := by
    have radiusOneLe : (1 : ℝ) ≤ radius := by
      exact_mod_cast radiusPos
    nlinarith
  have numeratorLtRadius :
      numerator <
        (radius : ℝ) * (absorption * ε ^ 2) := by
    exact
      (div_lt_iff₀ (mul_pos absorptionPos εSqPos)).1
        radiusGt
  have uniformRatioLt :
      numerator /
          (absorption * (radius : ℝ) ^ 2) <
        ε ^ 2 := by
    apply
      (div_lt_iff₀
        (mul_pos absorptionPos
          (sq_pos_of_pos radiusRealPos))).2
    calc
      numerator <
          (radius : ℝ) * (absorption * ε ^ 2) :=
        numeratorLtRadius
      _ ≤
          (radius : ℝ) ^ 2 * (absorption * ε ^ 2) :=
        mul_le_mul_of_nonneg_right radiusLeSquare
          (mul_nonneg absorptionPos.le εSqPos.le)
      _ =
          ε ^ 2 *
            (absorption * (radius : ℝ) ^ 2) := by
        ring
  refine ⟨radius, radiusPos, ?_⟩
  intro path
  rw [dist_eq_norm]
  have normSqLe :=
    generatedSpaceTime_projection_norm_sq_le_uniformTail
      θLtOne requestedTimePos radius radiusPos path
  have normSqLt :
      ‖generatedCriticalSpaceTimePath
            θLtOne requestedTimePos path -
          projectedGeneratedCriticalSpaceTimePath
            θLtOne requestedTimePos
            (lowFrequencyCube radius) path‖ ^ 2 <
        ε ^ 2 := by
    exact normSqLe.trans_lt (by
      simpa [numerator, absorption] using uniformRatioLt)
  nlinarith [
    norm_nonneg
      (generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path -
        projectedGeneratedCriticalSpaceTimePath
          θLtOne requestedTimePos
          (lowFrequencyCube radius) path)]

theorem generatedCriticalSpaceTimePathFamily_totallyBounded
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime) :
    TotallyBounded
      (generatedCriticalSpaceTimePathFamily
        (ν := ν) θLtOne requestedTimePos) := by
  rw [Metric.totallyBounded_iff]
  intro ε εPos
  have halfεPos : 0 < ε / 2 := by
    linarith
  obtain ⟨radius, radiusPos, uniformlyClose⟩ :=
    exists_lowFrequencyCube_uniformly_close
      (ν := ν) θLtOne requestedTimePos
      (ε / 2) halfεPos
  let compactSet : Set (SpaceTimeState requestedTime) :=
    compactObservedSpaceTimeSet
      (ν := ν) θLtOne requestedTimePos
      (lowFrequencyCube radius)
  have compactSetCompact : IsCompact compactSet := by
    exact compactObservedSpaceTimeSet_isCompact
      (ν := ν) θLtOne requestedTimePos
      (lowFrequencyCube radius)
  obtain ⟨centers, centersFinite, centersCover⟩ :=
    (Metric.totallyBounded_iff.mp
      compactSetCompact.totallyBounded)
      (ε / 2) halfεPos
  refine ⟨centers, centersFinite, ?_⟩
  intro member memberMem
  rcases memberMem with ⟨path, rfl⟩
  let projection : SpaceTimeState requestedTime :=
    projectedGeneratedCriticalSpaceTimePath
      θLtOne requestedTimePos
      (lowFrequencyCube radius) path
  have projectionMem : projection ∈ compactSet := by
    exact
      projectedGeneratedCriticalSpaceTimePath_mem_compactObserved
        (ν := ν) θLtOne requestedTimePos
        (lowFrequencyCube radius) path
  rcases Set.mem_iUnion.mp (centersCover projectionMem) with
    ⟨center, centerCover⟩
  rcases Set.mem_iUnion.mp centerCover with
    ⟨centerMem, projectionInBall⟩
  refine Set.mem_iUnion.mpr ⟨center, ?_⟩
  refine Set.mem_iUnion.mpr ⟨centerMem, ?_⟩
  rw [Metric.mem_ball] at projectionInBall ⊢
  have memberClose :
      dist
          (generatedCriticalSpaceTimePath
            θLtOne requestedTimePos path)
          projection <
        ε / 2 := by
    exact uniformlyClose path
  calc
    dist
        (generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path)
        center ≤
      dist
          (generatedCriticalSpaceTimePath
            θLtOne requestedTimePos path)
          projection +
        dist projection center :=
      dist_triangle _ _ _
    _ < ε := by
      linarith

theorem generatedCriticalSpaceTimePathFamily_isCompact_closure
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime) :
    IsCompact
      (closure
        (generatedCriticalSpaceTimePathFamily
          (ν := ν) θLtOne requestedTimePos)) := by
  exact
    (generatedCriticalSpaceTimePathFamily_totallyBounded
      (ν := ν) θLtOne requestedTimePos).closure.isCompact_of_isClosed
      isClosed_closure

end

end ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
end NavierStokes
end SaturationMonoid
