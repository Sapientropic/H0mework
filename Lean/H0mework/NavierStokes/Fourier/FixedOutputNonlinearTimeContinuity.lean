import Mathlib.MeasureTheory.Integral.MeanInequalities
import H0mework.NavierStokes.Fourier.FixedOutputNonlinearContinuity

/-!
# Time-integrated continuity of one fixed nonlinear Fourier row

The cutoff-independent pointwise row estimate becomes a quantitative
space-time stability law on every common finite Fourier carrier:

```text
integral ‖N(left(t))(k) - N(right(t))(k)‖
  ≤ 4 sqrt(|k|²) sqrt(E) sqrt(T)
      sqrt(integral Mass(left(t) - right(t))).
```

Here `E` is a common pointwise vorticity-mass ceiling.  The proof uses time
Cauchy--Schwarz after the fixed-output discrete Cauchy--Schwarz theorem.
Neither the constant nor the theorem mouth contains a cutoff, maximal
frequency, carrier cardinality, target limit, or continuation witness.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFixedOutputNonlinearTimeContinuity

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity

noncomputable section

/-! ## Continuity of the finite scalar ledgers -/

theorem finiteStateVorticityMass_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityMass modes state := by
  unfold finiteStateVorticityMass
  exact Finset.sum_nonneg fun wave waveMem =>
    complexCoordinateVectorNormSq_nonneg (state wave)

/-- Finite vorticity mass is a continuous scalar readout on the common
ambient Hilbert carrier. -/
theorem finiteStateVorticityMass_continuous
    (modes : Finset IntegerWavevector) :
    Continuous
      (fun state : ComplexVorticityHilbertState =>
        finiteStateVorticityMass modes state) := by
  unfold finiteStateVorticityMass
  apply continuous_finsetSum
  intro wave waveMem
  unfold complexCoordinateVectorNormSq
  apply continuous_finsetSum
  intro coordinate coordinateMem
  exact
    Complex.continuous_normSq.comp
      ((continuous_apply coordinate).comp
        (complexVorticityEvaluation_contDiff wave).continuous)

theorem finiteStateVorticityDifferenceMass_continuousOn
    (modes : Finset IntegerWavevector)
    (left right : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (leftContinuous : ContinuousOn left (Icc a b))
    (rightContinuous : ContinuousOn right (Icc a b)) :
    ContinuousOn
      (fun t =>
        finiteStateVorticityMass modes (left t - right t))
      (Icc a b) := by
  exact
    (finiteStateVorticityMass_continuous modes).comp_continuousOn
      (leftContinuous.sub rightContinuous)

theorem fixedOutputNonlinearDifferenceNorm_continuousOn
    (modes : Finset IntegerWavevector)
    (left right : ℝ → ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (a b : ℝ)
    (leftContinuous : ContinuousOn left (Icc a b))
    (rightContinuous : ContinuousOn right (Icc a b)) :
    ContinuousOn
      (fun t =>
        ‖finiteStateVorticityNonlinearCoefficientAt
              modes (left t) output -
            finiteStateVorticityNonlinearCoefficientAt
              modes (right t) output‖)
      (Icc a b) := by
  exact
    (((finiteStateVorticityNonlinearCoefficientAt_contDiff
          modes output).continuous.comp_continuousOn leftContinuous).sub
      ((finiteStateVorticityNonlinearCoefficientAt_contDiff
          modes output).continuous.comp_continuousOn rightContinuous)).norm

/-! ## Time Cauchy--Schwarz for a generated nonnegative mass -/

private theorem intervalIntegral_sqrt_le_sqrt_length_mul_sqrt_integral
    (mass : ℝ → ℝ)
    (a b : ℝ)
    (hab : a ≤ b)
    (massContinuous : ContinuousOn mass (Icc a b))
    (massNonneg : ∀ t ∈ Icc a b, 0 ≤ mass t) :
    (∫ t in a..b, Real.sqrt (mass t)) ≤
      Real.sqrt (b - a) *
        Real.sqrt (∫ t in a..b, mass t) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have sqrtContinuous :
      ContinuousOn (fun t => Real.sqrt (mass t)) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn massContinuous
  have sqrtSqContinuous :
      ContinuousOn
        (fun t => Real.sqrt (mass t) ^ 2)
        (Icc a b) :=
    sqrtContinuous.pow 2
  have sqrtIntegrable :
      Integrable (fun t => Real.sqrt (mass t)) μ := by
    change IntegrableOn (fun t => Real.sqrt (mass t)) (Ioc a b)
    exact
      sqrtContinuous.integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  have sqrtSqIntegrable :
      Integrable (fun t => Real.sqrt (mass t) ^ 2) μ := by
    change IntegrableOn
      (fun t => Real.sqrt (mass t) ^ 2) (Ioc a b)
    exact
      sqrtSqContinuous.integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  have sqrtMemLpNat :
      MemLp (fun t => Real.sqrt (mass t)) 2 μ :=
    (memLp_two_iff_integrable_sq
      sqrtIntegrable.aestronglyMeasurable).mpr sqrtSqIntegrable
  have sqrtMemLp :
      MemLp (fun t => Real.sqrt (mass t))
        (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using sqrtMemLpNat
  have oneMemLp :
      MemLp (fun _ : ℝ => (1 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) μ :=
    memLp_const 1
  have cauchy :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (μ := μ)
      (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t => Real.sqrt (mass t))
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg (mass t))
      oneMemLp sqrtMemLp
  have measureReal : μ.real univ = b - a := by
    dsimp [μ]
    rw [measureReal_def, Measure.restrict_apply_univ,
      Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have cauchySqrt :
      ∫ t, Real.sqrt (mass t) ∂μ ≤
        Real.sqrt (b - a) *
          Real.sqrt
            (∫ t, Real.sqrt (mass t) ^ 2 ∂μ) := by
    norm_num [measureReal, Real.sqrt_eq_rpow] at cauchy ⊢
    exact cauchy
  have squareIntegral :
      (∫ t, Real.sqrt (mass t) ^ 2 ∂μ) =
        ∫ t, mass t ∂μ := by
    apply integral_congr_ae
    change
      ∀ᵐ t ∂volume.restrict (Ioc a b),
        Real.sqrt (mass t) ^ 2 = mass t
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t timeMem
    exact Real.sq_sqrt (massNonneg t ⟨timeMem.1.le, timeMem.2⟩)
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  change
    (∫ t, Real.sqrt (mass t) ∂μ) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t, mass t ∂μ)
  simpa only [squareIntegral] using cauchySqrt

/-!
The two-function form is the exact time estimate needed for the whole
ambient nonlinear row: it consumes `L²_t × L²_t` directly and introduces
neither a pointwise ceiling nor a factor depending on the interval length.
-/
theorem intervalIntegral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq
    (left right : ℝ → ℝ)
    (a b : ℝ)
    (hab : a ≤ b)
    (leftContinuous : ContinuousOn left (Icc a b))
    (rightContinuous : ContinuousOn right (Icc a b))
    (leftNonneg : ∀ t ∈ Icc a b, 0 ≤ left t)
    (rightNonneg : ∀ t ∈ Icc a b, 0 ≤ right t) :
    (∫ t in a..b, left t * right t) ≤
      Real.sqrt (∫ t in a..b, left t ^ 2) *
        Real.sqrt (∫ t in a..b, right t ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have leftIntegrable : Integrable left μ := by
    change IntegrableOn left (Ioc a b)
    exact leftContinuous.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have rightIntegrable : Integrable right μ := by
    change IntegrableOn right (Ioc a b)
    exact rightContinuous.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have leftSqIntegrable : Integrable (fun t => left t ^ 2) μ := by
    change IntegrableOn (fun t => left t ^ 2) (Ioc a b)
    exact (leftContinuous.pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have rightSqIntegrable : Integrable (fun t => right t ^ 2) μ := by
    change IntegrableOn (fun t => right t ^ 2) (Ioc a b)
    exact (rightContinuous.pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have leftMemLpNat : MemLp left 2 μ :=
    (memLp_two_iff_integrable_sq
      leftIntegrable.aestronglyMeasurable).mpr leftSqIntegrable
  have rightMemLpNat : MemLp right 2 μ :=
    (memLp_two_iff_integrable_sq
      rightIntegrable.aestronglyMeasurable).mpr rightSqIntegrable
  have leftMemLp :
      MemLp left (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using leftMemLpNat
  have rightMemLp :
      MemLp right (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using rightMemLpNat
  have cauchy :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (μ := μ)
      (f := left)
      (g := right)
      (by
        change ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ left t
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t timeMem
        exact leftNonneg t ⟨timeMem.1.le, timeMem.2⟩)
      (by
        change ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ right t
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t timeMem
        exact rightNonneg t ⟨timeMem.1.le, timeMem.2⟩)
      leftMemLp rightMemLp
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  change
    (∫ t, left t * right t ∂μ) ≤
      Real.sqrt (∫ t, left t ^ 2 ∂μ) *
        Real.sqrt (∫ t, right t ^ 2 ∂μ)
  norm_num [Real.sqrt_eq_rpow] at cauchy ⊢
  exact cauchy

/-! ## Fixed-output space-time stability -/

/--
Time-integrated cutoff-independent continuity of one complete nonlinear
Fourier row.

The two trajectories need only be continuous and transverse on the same
finite carrier.  Their masses share a pointwise ceiling `energyCeiling`.
The right-hand side is the square root of the actual whole-carrier
space-time difference mass, so strong `L²_t` convergence forces strong
`L¹_t` convergence of every fixed nonlinear row.
-/
theorem
    finiteStateVorticityNonlinearCoefficientAt_sub_norm_intervalIntegral_le
    (modes : Finset IntegerWavevector)
    (left right : ℝ → ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (time energyCeiling : ℝ)
    (timeNonneg : 0 ≤ time)
    (leftContinuous : ContinuousOn left (Icc (0 : ℝ) time))
    (rightContinuous : ContinuousOn right (Icc (0 : ℝ) time))
    (leftTransverse :
      ∀ t ∈ Icc (0 : ℝ) time,
        FiniteStateTransverseOn modes (left t))
    (rightTransverse :
      ∀ t ∈ Icc (0 : ℝ) time,
        FiniteStateTransverseOn modes (right t))
    (massCeiling :
      ∀ t ∈ Icc (0 : ℝ) time,
        finiteStateVorticityMass modes (left t) ≤ energyCeiling ∧
          finiteStateVorticityMass modes (right t) ≤ energyCeiling) :
    (∫ t in (0 : ℝ)..time,
        ‖finiteStateVorticityNonlinearCoefficientAt
              modes (left t) output -
            finiteStateVorticityNonlinearCoefficientAt
              modes (right t) output‖) ≤
      4 * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt energyCeiling *
        Real.sqrt time *
        Real.sqrt
          (∫ t in (0 : ℝ)..time,
            finiteStateVorticityMass modes (left t - right t)) := by
  have zeroTimeMem : (0 : ℝ) ∈ Icc (0 : ℝ) time :=
    ⟨le_rfl, timeNonneg⟩
  have energyCeilingNonneg : 0 ≤ energyCeiling :=
    (finiteStateVorticityMass_nonneg modes (left 0)).trans
      (massCeiling 0 zeroTimeMem).1
  have differenceMassContinuous :
      ContinuousOn
        (fun t =>
          finiteStateVorticityMass modes (left t - right t))
        (Icc (0 : ℝ) time) :=
    finiteStateVorticityDifferenceMass_continuousOn
      modes left right 0 time leftContinuous rightContinuous
  have differenceSqrtContinuous :
      ContinuousOn
        (fun t =>
          Real.sqrt
            (finiteStateVorticityMass modes (left t - right t)))
        (Icc (0 : ℝ) time) :=
    Real.continuous_sqrt.comp_continuousOn differenceMassContinuous
  have nonlinearNormContinuous :
      ContinuousOn
        (fun t =>
          ‖finiteStateVorticityNonlinearCoefficientAt
                modes (left t) output -
              finiteStateVorticityNonlinearCoefficientAt
                modes (right t) output‖)
        (Icc (0 : ℝ) time) :=
    fixedOutputNonlinearDifferenceNorm_continuousOn
      modes left right output 0 time leftContinuous rightContinuous
  let coefficient : ℝ :=
    4 * Real.sqrt (integerWaveNormSq output) *
      Real.sqrt energyCeiling
  have coefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have pointwise :
      ∀ t ∈ Icc (0 : ℝ) time,
        ‖finiteStateVorticityNonlinearCoefficientAt
              modes (left t) output -
            finiteStateVorticityNonlinearCoefficientAt
              modes (right t) output‖ ≤
          coefficient *
            Real.sqrt
              (finiteStateVorticityMass
                modes (left t - right t)) := by
    intro t timeMem
    have sqrtLeftLe :
        Real.sqrt (finiteStateVorticityMass modes (left t)) ≤
          Real.sqrt energyCeiling :=
      Real.sqrt_le_sqrt (massCeiling t timeMem).1
    have sqrtRightLe :
        Real.sqrt (finiteStateVorticityMass modes (right t)) ≤
          Real.sqrt energyCeiling :=
      Real.sqrt_le_sqrt (massCeiling t timeMem).2
    have sqrtSumLe :
        Real.sqrt (finiteStateVorticityMass modes (left t)) +
            Real.sqrt (finiteStateVorticityMass modes (right t)) ≤
          2 * Real.sqrt energyCeiling := by
      linarith
    have base :=
      finiteStateVorticityNonlinearCoefficientAt_sub_norm_le_mass
        modes (left t) (right t)
        (leftTransverse t timeMem)
        (rightTransverse t timeMem) output
    calc
      ‖finiteStateVorticityNonlinearCoefficientAt
            modes (left t) output -
          finiteStateVorticityNonlinearCoefficientAt
            modes (right t) output‖ ≤
          2 * Real.sqrt (integerWaveNormSq output) *
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)) *
            (Real.sqrt (finiteStateVorticityMass modes (left t)) +
              Real.sqrt (finiteStateVorticityMass modes (right t))) :=
        base
      _ ≤
          2 * Real.sqrt (integerWaveNormSq output) *
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)) *
            (2 * Real.sqrt energyCeiling) :=
        mul_le_mul_of_nonneg_left sqrtSumLe
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))
      _ =
          coefficient *
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)) := by
        dsimp [coefficient]
        ring
  have nonlinearIntegrable :
      IntervalIntegrable
        (fun t =>
          ‖finiteStateVorticityNonlinearCoefficientAt
                modes (left t) output -
              finiteStateVorticityNonlinearCoefficientAt
                modes (right t) output‖)
        volume 0 time :=
    ContinuousOn.intervalIntegrable_of_Icc
      timeNonneg nonlinearNormContinuous
  have majorantIntegrable :
      IntervalIntegrable
        (fun t =>
          coefficient *
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)))
        volume 0 time :=
    ContinuousOn.intervalIntegrable_of_Icc timeNonneg
      (continuousOn_const.mul differenceSqrtContinuous)
  have integratedPointwise :
      (∫ t in (0 : ℝ)..time,
          ‖finiteStateVorticityNonlinearCoefficientAt
                modes (left t) output -
              finiteStateVorticityNonlinearCoefficientAt
                modes (right t) output‖) ≤
        ∫ t in (0 : ℝ)..time,
          coefficient *
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)) :=
    intervalIntegral.integral_mono_on
      timeNonneg nonlinearIntegrable majorantIntegrable pointwise
  have timeCauchy :
      (∫ t in (0 : ℝ)..time,
          Real.sqrt
            (finiteStateVorticityMass modes (left t - right t))) ≤
        Real.sqrt time *
          Real.sqrt
            (∫ t in (0 : ℝ)..time,
              finiteStateVorticityMass modes (left t - right t)) :=
    by
      simpa only [sub_zero] using
        intervalIntegral_sqrt_le_sqrt_length_mul_sqrt_integral
          (fun t =>
            finiteStateVorticityMass modes (left t - right t))
          0 time timeNonneg differenceMassContinuous
          (fun t timeMem =>
            finiteStateVorticityMass_nonneg
              modes (left t - right t))
  calc
    (∫ t in (0 : ℝ)..time,
        ‖finiteStateVorticityNonlinearCoefficientAt
              modes (left t) output -
            finiteStateVorticityNonlinearCoefficientAt
              modes (right t) output‖) ≤
        ∫ t in (0 : ℝ)..time,
          coefficient *
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)) :=
      integratedPointwise
    _ =
        coefficient *
          ∫ t in (0 : ℝ)..time,
            Real.sqrt
              (finiteStateVorticityMass modes (left t - right t)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤
        coefficient *
          (Real.sqrt time *
            Real.sqrt
              (∫ t in (0 : ℝ)..time,
                finiteStateVorticityMass modes (left t - right t))) :=
      mul_le_mul_of_nonneg_left timeCauchy coefficientNonneg
    _ =
        4 * Real.sqrt (integerWaveNormSq output) *
          Real.sqrt energyCeiling *
          Real.sqrt time *
          Real.sqrt
            (∫ t in (0 : ℝ)..time,
              finiteStateVorticityMass modes (left t - right t)) := by
      dsimp [coefficient]
      ring

end

end ThreeDimensionalVorticityCoefficientFixedOutputNonlinearTimeContinuity
end NavierStokes
end SaturationMonoid
