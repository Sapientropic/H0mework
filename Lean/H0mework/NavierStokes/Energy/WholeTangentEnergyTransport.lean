import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeViscousNegativeOne
import H0mework.NavierStokes.ShellSources.WholeContinuousMild
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Exact energy transport for an integrable whole tangent

This module supplies the vector-valued absolute-continuity step needed to
turn the source-generated `L²_t H⁻¹_x` whole tangent into an exact
finite-frequency energy ledger.

For an arbitrary integrable coefficient tangent `g`, the actual update

```text
u(t) = u₀ + ∫ₐᵗ g(s) ds
```

has absolutely continuous Euclidean coefficient energy and satisfies the
exact endpoint identity

```text
|u(b)|² - |u(a)|² = 2 ∫ₐᵇ ⟪u(t), g(t)⟫ dt.
```

The interval, tangent, and initial row are arbitrary.  No cutoff, terminal
frequency, differentiability witness, endpoint value, or continuation
conclusion is accepted as input.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport

open scoped BigOperators Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

private theorem absolutelyContinuousOnInterval_const
    {E : Type*}
    [SeminormedAddCommGroup E]
    (value : E)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun _ : ℝ => value) a b :=
  (LipschitzWith.const value).lipschitzOnWith
    |>.absolutelyContinuousOnInterval

/--
An absolutely continuous path remains absolutely continuous after an
arbitrary continuous linear observation.
-/
theorem AbsolutelyContinuousOnInterval.comp_continuousLinearMap
    {E F : Type*}
    [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F]
    [NormedSpace ℝ E]
    [NormedSpace ℝ F]
    (map : E →L[ℝ] F)
    {path : ℝ → E}
    {a b : ℝ}
    (pathAC : AbsolutelyContinuousOnInterval path a b) :
    AbsolutelyContinuousOnInterval (fun time => map (path time)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at pathAC ⊢
  intro ε εPos
  have denominatorPos : 0 < ‖map‖ + 1 := by positivity
  obtain ⟨δ, δPos, controls⟩ :=
    pathAC (ε / (‖map‖ + 1))
      (div_pos εPos denominatorPos)
  refine ⟨δ, δPos, fun intervals intervalsWithin totalLengthLt => ?_⟩
  have pathControl :=
    controls intervals intervalsWithin totalLengthLt
  calc
    ∑ index ∈ Finset.range intervals.1,
        dist
          (map (path (intervals.2 index).1))
          (map (path (intervals.2 index).2)) ≤
        ∑ index ∈ Finset.range intervals.1,
          ‖map‖ *
            dist
              (path (intervals.2 index).1)
              (path (intervals.2 index).2) := by
      apply Finset.sum_le_sum
      intro index indexMem
      simpa only [dist_eq_norm, ← map.map_sub] using
        map.le_opNorm
          (path (intervals.2 index).1 -
            path (intervals.2 index).2)
    _ =
        ‖map‖ *
          ∑ index ∈ Finset.range intervals.1,
            dist
              (path (intervals.2 index).1)
              (path (intervals.2 index).2) := by
      rw [Finset.mul_sum]
    _ ≤
        ‖map‖ * (ε / (‖map‖ + 1)) := by
      exact
        mul_le_mul_of_nonneg_left pathControl.le
          (norm_nonneg map)
    _ <
        (‖map‖ + 1) * (ε / (‖map‖ + 1)) := by
      exact
        mul_lt_mul_of_pos_right
          (lt_add_one ‖map‖)
          (div_pos εPos denominatorPos)
    _ = ε := by
      field_simp [denominatorPos.ne']

/--
The indefinite Bochner integral of an interval-integrable vector field is
absolutely continuous.  Mathlib currently exposes this theorem for real
codomain; the same estimate is valid in every complete real normed space.
-/
theorem
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    {tangent : ℝ → E}
    {a b c : ℝ}
    (tangentIntegrable :
      IntervalIntegrable tangent volume a b)
    (cMem : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval
      (fun time => ∫ earlier in c..time, tangent earlier) a b := by
  let intervalsUnion :=
    fun intervals : ℕ × (ℕ → ℝ × ℝ) =>
      ⋃ index ∈ Finset.range intervals.1,
        uIoc (intervals.2 index).1 (intervals.2 index).2
  have finiteIntegral :
      (∫⁻ time in uIoc a b, ‖tangent time‖ₑ) < ⊤ :=
    by
      have tangentIntegrableOn :=
        intervalIntegrable_iff.mp tangentIntegrable
      exact tangentIntegrableOn.hasFiniteIntegral
  have integralTendsto :
      Tendsto
        (fun intervals =>
          ∫⁻ time in intervalsUnion intervals,
            ‖tangent time‖ₑ
            ∂volume.restrict (uIoc a b))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b))
        (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt finiteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        a b)
  have realIntegralTendsto :
      Tendsto
        (fun intervals =>
          (∫⁻ time in intervalsUnion intervals,
            ‖tangent time‖ₑ
            ∂volume.restrict (uIoc a b)).toReal)
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b))
        (𝓝 0) := by
    change
      Tendsto
        (ENNReal.toReal ∘
          fun intervals =>
            ∫⁻ time in intervalsUnion intervals,
              ‖tangent time‖ₑ
              ∂volume.restrict (uIoc a b))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b))
        (𝓝 0)
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp)).tendsto.comp
        integralTendsto
  refine squeeze_zero' ?_ ?_ realIntegralTendsto
  · filter_upwards with intervals
    exact Finset.sum_nonneg fun _ _ => dist_nonneg
  have eventuallyDisjoint :
      ∀ᶠ intervals :
          ℕ × (ℕ → ℝ × ℝ) in
        AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
        intervals ∈
          AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [eventuallyDisjoint] with
      intervals intervalsDisjoint
  have endpointsWithin := intervalsDisjoint.1
  have pairwiseDisjoint := intervalsDisjoint.2
  rw [
    ← integral_norm_eq_lintegral_enorm
      (tangentIntegrable.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp [uIoc]) pairwiseDisjoint]
  · apply Finset.sum_le_sum
    intro index indexMem
    have intervalSubset :
        uIoc (intervals.2 index).1
            (intervals.2 index).2 ⊆
          uIoc a b :=
      AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin
        intervalsDisjoint (Finset.mem_range.mp indexMem)
    rw [
      dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by
          apply IntervalIntegrable.mono_set' tangentIntegrable
          exact
            uIoc_subset_uIoc_of_uIcc_subset_uIcc
              (uIcc_subset_uIcc cMem
                (endpointsWithin index indexMem).1))
        (by
          apply IntervalIntegrable.mono_set' tangentIntegrable
          exact
            uIoc_subset_uIoc_of_uIcc_subset_uIcc
              (uIcc_subset_uIcc cMem
                (endpointsWithin index indexMem).2)),
      Measure.restrict_restrict_of_subset intervalSubset,
      intervalIntegral.integral_symm,
      norm_neg]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc
  · intro index indexMem
    unfold IntegrableOn
    have intervalSubset :
        uIoc (intervals.2 index).1
            (intervals.2 index).2 ⊆
          uIoc a b :=
      AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin
        intervalsDisjoint (Finset.mem_range.mp indexMem)
    rw [Measure.restrict_restrict_of_subset intervalSubset]
    exact
      IntegrableOn.mono_set
        tangentIntegrable.def'.norm intervalSubset

/-- The path generated by one actual integrable coefficient tangent. -/
def intervalIntegralComplexCoordinatePath
    (initial : ComplexCoordinateVector)
    (tangent : ℝ → ComplexCoordinateVector)
    (start : ℝ) :
    ℝ → ComplexCoordinateVector :=
  (fun _ => initial) +
    fun time => ∫ earlier in start..time, tangent earlier

theorem intervalIntegralComplexCoordinatePath_absolutelyContinuousOnInterval
    (initial : ComplexCoordinateVector)
    {tangent : ℝ → ComplexCoordinateVector}
    {a b : ℝ}
    (tangentIntegrable :
      IntervalIntegrable tangent volume a b) :
    AbsolutelyContinuousOnInterval
      (intervalIntegralComplexCoordinatePath initial tangent a)
      a b := by
  have constantAC :=
    absolutelyContinuousOnInterval_const initial a b
  have integralAC :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
      (c := a) tangentIntegrable (by simp)
  unfold intervalIntegralComplexCoordinatePath
  exact constantAC.add integralAC

private theorem absolutelyContinuousOnInterval_add_real
    {left right : ℝ → ℝ}
    {a b : ℝ}
    (leftAC : AbsolutelyContinuousOnInterval left a b)
    (rightAC : AbsolutelyContinuousOnInterval right a b) :
    AbsolutelyContinuousOnInterval
      (fun time => left time + right time) a b := by
  unfold AbsolutelyContinuousOnInterval at leftAC rightAC ⊢
  apply squeeze_zero (fun intervals => ?_)
      (fun intervals => ?_)
      (by simpa only [zero_add] using Tendsto.add leftAC rightAC)
  · exact Finset.sum_nonneg fun _ _ => dist_nonneg
  ·
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro index indexMem
    exact dist_add_add_le _ _ _ _

private theorem absolutelyContinuousOnInterval_sq
    {path : ℝ → ℝ}
    {a b : ℝ}
    (pathAC : AbsolutelyContinuousOnInterval path a b) :
    AbsolutelyContinuousOnInterval
      (fun time => path time ^ 2) a b := by
  obtain ⟨bound, boundProperty⟩ := pathAC.exists_bound
  let nonnegativeBound : ℝ := max bound 0
  have nonnegativeBoundNonneg : 0 ≤ nonnegativeBound :=
    le_max_right _ _
  have pathBound :
      ∀ time ∈ uIcc a b,
        |path time| ≤ nonnegativeBound := by
    intro time timeMem
    exact
      (boundProperty time timeMem).trans
        (le_max_left _ _)
  rw [absolutelyContinuousOnInterval_iff] at pathAC ⊢
  intro ε εPos
  have denominatorPos :
      0 < 2 * nonnegativeBound + 1 := by
    positivity
  obtain ⟨δ, δPos, controls⟩ :=
    pathAC (ε / (2 * nonnegativeBound + 1))
      (div_pos εPos denominatorPos)
  refine ⟨δ, δPos, fun intervals intervalsWithin totalLengthLt => ?_⟩
  have pathControl :=
    controls intervals intervalsWithin totalLengthLt
  calc
    ∑ index ∈ Finset.range intervals.1,
        dist
          (path (intervals.2 index).1 ^ 2)
          (path (intervals.2 index).2 ^ 2) ≤
        ∑ index ∈ Finset.range intervals.1,
          (2 * nonnegativeBound) *
            dist
              (path (intervals.2 index).1)
              (path (intervals.2 index).2) := by
      apply Finset.sum_le_sum
      intro index indexMem
      have firstMem :=
        (intervalsWithin.1 index indexMem).1
      have secondMem :=
        (intervalsWithin.1 index indexMem).2
      have sumBound :
          |path (intervals.2 index).1 +
            path (intervals.2 index).2| ≤
            2 * nonnegativeBound := by
        calc
          |path (intervals.2 index).1 +
              path (intervals.2 index).2| ≤
              |path (intervals.2 index).1| +
                |path (intervals.2 index).2| :=
            abs_add_le _ _
          _ ≤ nonnegativeBound + nonnegativeBound := by
            gcongr
            · exact pathBound _ firstMem
            · exact pathBound _ secondMem
          _ = 2 * nonnegativeBound := by ring
      rw [Real.dist_eq, Real.dist_eq, sq_sub_sq, abs_mul]
      exact
        mul_le_mul_of_nonneg_right sumBound
          (abs_nonneg _)
    _ =
        (2 * nonnegativeBound) *
          ∑ index ∈ Finset.range intervals.1,
            dist
              (path (intervals.2 index).1)
              (path (intervals.2 index).2) := by
      rw [Finset.mul_sum]
    _ ≤
        (2 * nonnegativeBound) *
          (ε / (2 * nonnegativeBound + 1)) := by
      exact
        mul_le_mul_of_nonneg_left pathControl.le
          (mul_nonneg (by norm_num) nonnegativeBoundNonneg)
    _ <
        (2 * nonnegativeBound + 1) *
          (ε / (2 * nonnegativeBound + 1)) := by
      exact
        mul_lt_mul_of_pos_right
          (lt_add_one (2 * nonnegativeBound))
          (div_pos εPos denominatorPos)
    _ = ε := by
      field_simp [denominatorPos.ne']

/--
The exact Euclidean coefficient amplitude remains absolutely continuous
along every absolutely continuous complex coefficient path.
-/
theorem
    AbsolutelyContinuousOnInterval.comp_complexCoordinateAmplitudeSq
    {path : ℝ → ComplexCoordinateVector}
    {a b : ℝ}
    (pathAC : AbsolutelyContinuousOnInterval path a b) :
    AbsolutelyContinuousOnInterval
      (fun time => complexCoordinateAmplitudeSq (path time))
      a b := by
  have coordinateAC :
      ∀ coordinate : Coordinate,
        AbsolutelyContinuousOnInterval
          (fun time => Complex.normSq (path time coordinate))
          a b := by
    intro coordinate
    let realCoordinate :
        ComplexCoordinateVector →L[ℝ] ℝ :=
      Complex.reCLM.comp
        (ContinuousLinearMap.proj coordinate)
    let imaginaryCoordinate :
        ComplexCoordinateVector →L[ℝ] ℝ :=
      Complex.imCLM.comp
        (ContinuousLinearMap.proj coordinate)
    have realAC :=
      AbsolutelyContinuousOnInterval.comp_continuousLinearMap
        realCoordinate pathAC
    have imaginaryAC :=
      AbsolutelyContinuousOnInterval.comp_continuousLinearMap
        imaginaryCoordinate pathAC
    have realSqAC :=
      absolutelyContinuousOnInterval_sq realAC
    have imaginarySqAC :=
      absolutelyContinuousOnInterval_sq imaginaryAC
    simpa only [realCoordinate, imaginaryCoordinate,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.normSq_apply, pow_two] using
        absolutelyContinuousOnInterval_add_real
          realSqAC imaginarySqAC
  unfold
    ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.complexCoordinateAmplitudeSq
  induction (Finset.univ : Finset Coordinate) using
      Finset.induction_on with
  | empty =>
      simpa using
        absolutelyContinuousOnInterval_const (0 : ℝ) a b
  | @insert coordinate tail coordinateNotMem inductionHypothesis =>
      simpa only [Finset.sum_insert coordinateNotMem] using
        absolutelyContinuousOnInterval_add_real
          (coordinateAC coordinate) inductionHypothesis

/--
Exact endpoint energy transport for an absolutely continuous coefficient
path whose actual tangent is identified almost everywhere.  This is the
update-law form consumed by source-generated mild paths: the path and
tangent must already live on the same interval carrier, but no endpoint
estimate or continuation conclusion is assumed.
-/
theorem
    AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity
    {path tangent : ℝ → ComplexCoordinateVector}
    {a b : ℝ}
    (pathAC : AbsolutelyContinuousOnInterval path a b)
    (pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc a b →
          HasDerivAt path (tangent time) time) :
    (∫ time in a..b,
        2 *
          complexCoordinateRealInner
            (path time) (tangent time)) =
      complexCoordinateAmplitudeSq (path b) -
        complexCoordinateAmplitudeSq (path a) := by
  have energyAC :
      AbsolutelyContinuousOnInterval
        (fun time => complexCoordinateAmplitudeSq (path time))
        a b :=
    AbsolutelyContinuousOnInterval.comp_complexCoordinateAmplitudeSq
      pathAC
  calc
    (∫ time in a..b,
        2 *
          complexCoordinateRealInner
            (path time) (tangent time)) =
        ∫ time in a..b,
          deriv
            (fun actual =>
              complexCoordinateAmplitudeSq (path actual))
            time := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [pathDerivative] with
          time derivative timeMem
      have actualDerivative :=
        complexCoordinateAmplitudeSq_hasDerivAt
          path time (tangent time)
          (derivative (uIoc_subset_uIcc timeMem))
      exact actualDerivative.deriv.symm
    _ =
        complexCoordinateAmplitudeSq (path b) -
          complexCoordinateAmplitudeSq (path a) :=
      energyAC.integral_deriv_eq_sub

/--
The coefficient-space heat/Duhamel path written in integrating-factor
coordinates.  `damping` is the exact viscous frequency multiplier; the
source term remains an arbitrary integrable coefficient row.
-/
def heatDuhamelComplexCoordinatePath
    (initial : ComplexCoordinateVector)
    (nonlinear : ℝ → ComplexCoordinateVector)
    (damping start : ℝ) :
    ℝ → ComplexCoordinateVector :=
  (fun time =>
    Real.exp (-damping * (time - start))) •
      intervalIntegralComplexCoordinatePath initial
        (fun earlier =>
          Real.exp (damping * (earlier - start)) •
            nonlinear earlier)
        start

private theorem heatDuhamelWeightedNonlinear_intervalIntegrable
    {nonlinear : ℝ → ComplexCoordinateVector}
    (damping start : ℝ)
    {a b : ℝ}
    (nonlinearIntegrable :
      IntervalIntegrable nonlinear volume a b) :
    IntervalIntegrable
      (fun time =>
        Real.exp (damping * (time - start)) •
          nonlinear time)
      volume a b :=
  nonlinearIntegrable.continuousOn_smul (by fun_prop)

private theorem heatDuhamelIntegratingFactorPath_absolutelyContinuousOnInterval
    (initial : ComplexCoordinateVector)
    {nonlinear : ℝ → ComplexCoordinateVector}
    (damping start : ℝ)
    {a b : ℝ}
    (nonlinearIntegrable :
      IntervalIntegrable nonlinear volume a b)
    (startMem : start ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval
      (intervalIntegralComplexCoordinatePath initial
        (fun time =>
          Real.exp (damping * (time - start)) •
            nonlinear time)
        start)
      a b := by
  have constantAC :=
    absolutelyContinuousOnInterval_const initial a b
  have integralAC :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
      (c := start)
      (heatDuhamelWeightedNonlinear_intervalIntegrable
        damping start nonlinearIntegrable)
      startMem
  unfold intervalIntegralComplexCoordinatePath
  exact constantAC.add integralAC

private theorem heatDuhamelDampingFactor_absolutelyContinuousOnInterval
    (damping start a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun time =>
        Real.exp (-damping * (time - start)))
      a b := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  fun_prop

theorem heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
    (initial : ComplexCoordinateVector)
    {nonlinear : ℝ → ComplexCoordinateVector}
    (damping start : ℝ)
    {a b : ℝ}
    (nonlinearIntegrable :
      IntervalIntegrable nonlinear volume a b)
    (startMem : start ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval
      (heatDuhamelComplexCoordinatePath
        initial nonlinear damping start)
      a b := by
  unfold heatDuhamelComplexCoordinatePath
  exact
    AbsolutelyContinuousOnInterval.smul
      (M := ℝ)
      (heatDuhamelDampingFactor_absolutelyContinuousOnInterval
        damping start a b)
      (heatDuhamelIntegratingFactorPath_absolutelyContinuousOnInterval
        initial damping start nonlinearIntegrable startMem)

theorem heatDuhamelComplexCoordinatePath_ae_hasDerivAt
    (initial : ComplexCoordinateVector)
    {nonlinear : ℝ → ComplexCoordinateVector}
    (damping start : ℝ)
    {a b : ℝ}
    (nonlinearIntegrable :
      IntervalIntegrable nonlinear volume a b)
    (startMem : start ∈ uIcc a b) :
    ∀ᵐ time : ℝ,
      time ∈ uIcc a b →
        HasDerivAt
          (heatDuhamelComplexCoordinatePath
            initial nonlinear damping start)
          (nonlinear time -
            damping •
              heatDuhamelComplexCoordinatePath
                initial nonlinear damping start time)
          time := by
  have weightedNonlinearIntegrable :
      IntervalIntegrable
        (fun time =>
          Real.exp (damping * (time - start)) •
            nonlinear time)
        volume a b :=
    heatDuhamelWeightedNonlinear_intervalIntegrable
      damping start nonlinearIntegrable
  filter_upwards [
    weightedNonlinearIntegrable.ae_hasDerivAt_integral] with
      time integralDerivative
  intro timeMem
  have actualIntegralDerivative :=
    integralDerivative timeMem start startMem
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
          (-damping) time :=
      by
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
    ring
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

/--
The integrating-factor path is exactly the usual causal heat/Duhamel
formula.  This identity is what identifies the abstractly integrated
tangent with the already generated mild row, without replacing either
carrier.
-/
theorem heatDuhamelComplexCoordinatePath_eq_heat_add_integral
    (initial : ComplexCoordinateVector)
    (nonlinear : ℝ → ComplexCoordinateVector)
    (damping start time : ℝ) :
    heatDuhamelComplexCoordinatePath
        initial nonlinear damping start time =
      Real.exp (-damping * (time - start)) • initial +
        ∫ earlier in start..time,
          Real.exp (-damping * (time - earlier)) •
            nonlinear earlier := by
  unfold heatDuhamelComplexCoordinatePath
    intervalIntegralComplexCoordinatePath
  change
    Real.exp (-damping * (time - start)) •
        (initial +
          ∫ earlier in start..time,
            Real.exp (damping * (earlier - start)) •
              nonlinear earlier) =
      _
  rw [smul_add, ← intervalIntegral.integral_smul]
  apply congrArg₂ (· + ·) rfl
  apply intervalIntegral.integral_congr
  intro earlier earlierMem
  dsimp
  rw [smul_smul, ← Real.exp_add]
  congr 1
  ring

/--
Exact endpoint energy law for a viscously damped coefficient row.  Frequency
growth, nonlinear amplitude, and viscous damping occur in the same actual
tangent before any norm estimate is taken.
-/
theorem heatDuhamelComplexCoordinatePath_energy_identity
    (initial : ComplexCoordinateVector)
    {nonlinear : ℝ → ComplexCoordinateVector}
    (damping : ℝ)
    {a b : ℝ}
    (nonlinearIntegrable :
      IntervalIntegrable nonlinear volume a b) :
    (∫ time in a..b,
        2 *
          complexCoordinateRealInner
            (heatDuhamelComplexCoordinatePath
              initial nonlinear damping a time)
            (nonlinear time -
              damping •
                heatDuhamelComplexCoordinatePath
                  initial nonlinear damping a time)) =
      complexCoordinateAmplitudeSq
          (heatDuhamelComplexCoordinatePath
            initial nonlinear damping a b) -
        complexCoordinateAmplitudeSq
          (heatDuhamelComplexCoordinatePath
            initial nonlinear damping a a) := by
  exact
    AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity
      (heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
        initial damping a nonlinearIntegrable (by simp))
      (heatDuhamelComplexCoordinatePath_ae_hasDerivAt
        initial damping a nonlinearIntegrable (by simp))

/-! ## The inherited common-time carrier as a real interval update -/

/--
Zero extension of a common-time coefficient row to the real line.  On the
physical interval this is definitionally the inherited row; outside it no
new source content is introduced.
-/
def commonTimeZeroExtension
    {E : Type*}
    [Zero E]
    (requestedTime : ℝ)
    (value : Icc (0 : ℝ) requestedTime → E) :
    ℝ → E :=
  fun time =>
    if timeMem : time ∈ Icc (0 : ℝ) requestedTime then
      value ⟨time, timeMem⟩
    else
      0

@[simp] theorem commonTimeZeroExtension_of_mem
    {E : Type*}
    [Zero E]
    (requestedTime : ℝ)
    (value : Icc (0 : ℝ) requestedTime → E)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    commonTimeZeroExtension requestedTime value time =
      value ⟨time, timeMem⟩ := by
  simp [commonTimeZeroExtension, timeMem]

private theorem commonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val :
          Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

/--
Every inherited common-time `L¹` row has an interval-integrable zero
extension.  This is the measure-theoretic seam needed by the actual
Bochner update, not an extra integrability premise.
-/
theorem commonTimeZeroExtension_intervalIntegrable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (value :
      MeasureTheory.Lp E 1
        (commonTimeMeasure requestedTime)) :
    IntervalIntegrable
      (commonTimeZeroExtension requestedTime value)
      volume 0 requestedTime := by
  rw [
    intervalIntegrable_iff_integrableOn_Icc_of_le
      requestedTimeNonneg,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc,
    ← commonTimeMeasure_eq_comap_volume requestedTime]
  apply (MeasureTheory.L1.integrable_coeFn value).congr
  filter_upwards with time
  simp only [Function.comp_apply]
  rw [commonTimeZeroExtension_of_mem
    requestedTime value time.1 time.property]

/-! ## Same-receipt whole-path energy transport -/

section ActualWholeContinuousReceipt

variable
  {lineage : GeneratedIntegerShellInfiniteLineage}
  {ν : Viscosity}
  {θ requestedTime : ℝ}
  {θLtOne : θ < 1}
  {criticalMargin :
    ∀ length : ℕ,
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport (lineage.current length))
            (generatedComplexVorticityState
              (lineage.current length)
              (generatedSupport (lineage.current length))) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
  {requestedTimePos : 0 < requestedTime}

/--
The actual nonlinear row of a whole continuous mild receipt, installed on
the real interval carrier used by the update law.
-/
def WholeContinuousMildReceipt.actualWaveNonlinearExtension
    (receipt :
      WholeContinuousMildReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  commonTimeZeroExtension requestedTime
    (transverseSpaceTimeNonlinearRow
      receipt.transverseLimit wave)

theorem
    WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
    (receipt :
      WholeContinuousMildReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension
        receipt wave)
      volume 0 requestedTime := by
  exact
    commonTimeZeroExtension_intervalIntegrable
      requestedTime requestedTimePos.le
      (transverseSpaceTimeNonlinearRow
        receipt.transverseLimit wave)

/--
The real-line representative of one nonzero whole mild row, formed from
the inherited initial state and actual nonlinear row with its exact
frequency-dependent viscous damping.
-/
def WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
    (receipt :
      WholeContinuousMildReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath
    (receipt.initialState wave)
    (WholeContinuousMildReceipt.actualWaveNonlinearExtension
      receipt wave)
    (ν.coeff * integerWaveViscousMultiplier wave)
    0

/--
The source-generated whole path and the integrating-factor update are the
same pointwise coefficient path on the complete requested interval.
-/
theorem WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
    (receipt :
      WholeContinuousMildReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    receipt.wholePath time wave =
      WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
        receipt wave time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime requestedTimePos.le time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier) wave •
          WholeContinuousMildReceipt.actualWaveNonlinearExtension
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
            WholeContinuousMildReceipt.actualWaveNonlinearExtension
              receipt wave earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    filter_upwards with earlier
    rw [WholeContinuousMildReceipt.actualWaveNonlinearExtension,
      commonTimeZeroExtension_of_mem
        requestedTime
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave)
        earlier.1 earlier.property]
  rw [receipt.wholePath_mild_identity wave waveNe time,
    weightedDuhamelAt_eq_actual_nonlinear_integral
      receipt.toInfiniteMildDuhamelForcingReceipt
      wave waveNe time,
    convertedIntegral']
  unfold WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

/--
Exact same-receipt endpoint energy law for every actual nonzero Fourier
row.  The integrand is the genuine nonlinear coefficient minus the exact
frequency-weighted viscous row; the right side uses the generated whole
path endpoints.
-/
theorem WholeContinuousMildReceipt.actualWave_endpointEnergy_identity
    (receipt :
      WholeContinuousMildReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    (∫ time in (0 : ℝ)..requestedTime,
        2 *
          complexCoordinateRealInner
            (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              receipt wave time)
            (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                receipt wave time -
              (ν.coeff * integerWaveViscousMultiplier wave) •
                WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                  receipt wave time)) =
      complexCoordinateAmplitudeSq
          (receipt.wholePath
            ⟨requestedTime,
              ⟨requestedTimePos.le, le_rfl⟩⟩ wave) -
        complexCoordinateAmplitudeSq
          (receipt.initialState wave) := by
  have energyIdentity :=
    heatDuhamelComplexCoordinatePath_energy_identity
      (receipt.initialState wave)
      (nonlinear :=
        WholeContinuousMildReceipt.actualWaveNonlinearExtension
          receipt wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        receipt wave)
  rw [show
      WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt wave =
        heatDuhamelComplexCoordinatePath
          (receipt.initialState wave)
          (WholeContinuousMildReceipt.actualWaveNonlinearExtension
            receipt wave)
          (ν.coeff * integerWaveViscousMultiplier wave)
          0 by rfl]
  rw [energyIdentity]
  have terminalEq :=
    WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
      receipt
      wave waveNe
      ⟨requestedTime, ⟨requestedTimePos.le, le_rfl⟩⟩
  have initialPathEq :=
    WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
      receipt
      wave waveNe
      ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩
  have initialEq :
      receipt.wholePath
          ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ wave =
        receipt.initialState wave := by
    rw [receipt.wholePath_initial]
  have terminalEq' :
      heatDuhamelComplexCoordinatePath
          (receipt.initialState wave)
          (WholeContinuousMildReceipt.actualWaveNonlinearExtension
            receipt wave)
          (ν.coeff * integerWaveViscousMultiplier wave)
          0 requestedTime =
        receipt.wholePath
          ⟨requestedTime,
            ⟨requestedTimePos.le, le_rfl⟩⟩ wave := by
    simpa only [
      WholeContinuousMildReceipt.actualWaveHeatDuhamelPath] using
        terminalEq.symm
  have initialPathEq' :
      heatDuhamelComplexCoordinatePath
          (receipt.initialState wave)
          (WholeContinuousMildReceipt.actualWaveNonlinearExtension
            receipt wave)
          (ν.coeff * integerWaveViscousMultiplier wave)
          0 0 =
        receipt.wholePath
          ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ wave := by
    simpa only [
      WholeContinuousMildReceipt.actualWaveHeatDuhamelPath] using
        initialPathEq.symm
  rw [terminalEq', initialPathEq', initialEq]

end ActualWholeContinuousReceipt

/--
Exact energy transport for an arbitrary integrable coefficient tangent.
The derivative is generated almost everywhere by the Bochner update, then
written back as an endpoint identity.
-/
theorem intervalIntegralComplexCoordinatePath_energy_identity
    (initial : ComplexCoordinateVector)
    {tangent : ℝ → ComplexCoordinateVector}
    {a b : ℝ}
    (tangentIntegrable :
      IntervalIntegrable tangent volume a b) :
    (∫ time in a..b,
        2 *
          complexCoordinateRealInner
            (intervalIntegralComplexCoordinatePath
              initial tangent a time)
            (tangent time)) =
      complexCoordinateAmplitudeSq
          (intervalIntegralComplexCoordinatePath
            initial tangent a b) -
        complexCoordinateAmplitudeSq
          (intervalIntegralComplexCoordinatePath
            initial tangent a a) := by
  let path : ℝ → ComplexCoordinateVector :=
    intervalIntegralComplexCoordinatePath initial tangent a
  have pathAC :
      AbsolutelyContinuousOnInterval path a b :=
    intervalIntegralComplexCoordinatePath_absolutelyContinuousOnInterval
      initial tangentIntegrable
  have pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc a b →
          HasDerivAt path (tangent time) time := by
    filter_upwards [
      tangentIntegrable.ae_hasDerivAt_integral] with
        time integralDerivative
    intro timeMem
    have actualIntegralDerivative :=
      integralDerivative timeMem a (by simp)
    change
      HasDerivAt
        ((fun _ : ℝ => initial) +
          fun actual =>
            ∫ earlier in a..actual, tangent earlier)
        (tangent time) time
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const time initial).add
        actualIntegralDerivative
  simpa only [path] using
    AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity
      pathAC pathDerivative

end

end ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
end NavierStokes
end SaturationMonoid
