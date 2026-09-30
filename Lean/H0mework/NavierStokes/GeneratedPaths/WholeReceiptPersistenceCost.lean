import H0mework.NavierStokes.Galerkin.TimeEquicontinuity
import H0mework.NavierStokes.GeneratedPaths.WholeReceiptPersistence

/-!
# Quantitative persistence cost of a whole generated receipt

This module keeps every source receipt as a complete flattened support.  The
actual finite Galerkin update and time Cauchy--Schwarz will give

```text
D_receipt(a,b)
  ≤ 3 (b-a) (2π)² selectedShellSq
      ∫ₐᵇ ‖∂ₜω‖²_{H⁻¹(row)}.
```

The factor `3` is the exact finite coordinate-cardinality loss between the
repository's row sup norm and the three scalar coordinates.  There is no
whole-shell cardinality factor: all waves are summed inside the common
negative-one mass before the bound is taken.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistenceCost

open scoped BigOperators Interval ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNegativeSobolevTimeBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinTimeEquicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistence

noncomputable section

/-! ## Pointwise whole-receipt tangent density -/

/-- Complete squared scalar-coordinate mass of one tangent on the exact
nonzero flattened support written by a receipt. -/
def receiptSupportTangentEnergy
    (receipt : GeneratedIntegerShellReceipt)
    (tangent : ComplexVorticityHilbertState) : ℝ :=
  ∑ index ∈ (generatedIntegerShellReceiptTrace receipt).support,
    Complex.normSq (tangent index.1 index.2)

theorem receiptSupportTangentEnergy_nonneg
    (receipt : GeneratedIntegerShellReceipt)
    (tangent : ComplexVorticityHilbertState) :
    0 ≤ receiptSupportTangentEnergy receipt tangent := by
  unfold receiptSupportTangentEnergy
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem complexCoordinateAmplitudeSq_le_three_mul_norm_sq
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq vector ≤ 3 * ‖vector‖ ^ 2 := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate,
      Complex.normSq (vector coordinate)) ≤
        ∑ _coordinate : Coordinate, ‖vector‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate coordinateMem
      rw [Complex.normSq_eq_norm_sq]
      exact
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
          (norm_le_pi_norm vector coordinate)
    _ = 3 * ‖vector‖ ^ 2 := by
      norm_num [Fin.sum_univ_succ]

private theorem receiptWave_ne_zero
    (receipt : GeneratedIntegerShellReceipt)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ receipt.wholeShellModes) :
    wave ≠ 0 := by
  intro waveZero
  have waveShell :
      integerWaveShellSq wave = receipt.selectedShellSq :=
    ((mem_generatedOuterNonlinearShellModes_iff
      receipt.current receipt.selectedShellSq wave).mp waveMem).2
  rw [waveZero, integerWaveShellSq_zero] at waveShell
  have shellPos :=
    generatedIntegerShellReceipt_selectedShellSq_pos receipt
  omega

private theorem receiptWave_multiplier
    (receipt : GeneratedIntegerShellReceipt)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ receipt.wholeShellModes) :
    integerWaveViscousMultiplier wave =
      (2 * Real.pi) ^ 2 *
        (receipt.selectedShellSq : ℝ) := by
  unfold integerWaveViscousMultiplier
  rw [integerWaveNormSq_eq_integerWaveShellSq]
  have waveShell :
      integerWaveShellSq wave = receipt.selectedShellSq :=
    ((mem_generatedOuterNonlinearShellModes_iff
      receipt.current receipt.selectedShellSq wave).mp waveMem).2
  rw [waveShell]

private theorem receiptSupport_subset_wholeShell_product
    (receipt : GeneratedIntegerShellReceipt) :
    (generatedIntegerShellReceiptTrace receipt).support ⊆
      receipt.wholeShellModes ×ˢ
        (Finset.univ : Finset Coordinate) := by
  intro index indexMem
  rw [Finset.mem_product]
  exact
    ⟨(mem_generatedIntegerShellTrace_support_iff
      receipt.current receipt.selectedShellSq index).mp indexMem |>.1,
      Finset.mem_univ _⟩

/-- The complete tangent density on one receipt support is controlled by the
global row-negative-one mass with exactly one selected-shell multiplier.
There is no factor depending on the number of waves in the shell. -/
theorem receiptSupportTangentEnergy_le_three_shell_negativeOneMass
    (modes : Finset IntegerWavevector)
    (receipt : GeneratedIntegerShellReceipt)
    (wholeShellSubset : receipt.wholeShellModes ⊆ modes)
    (tangent : ComplexVorticityHilbertState) :
    receiptSupportTangentEnergy receipt tangent ≤
      3 * (2 * Real.pi) ^ 2 *
          (receipt.selectedShellSq : ℝ) *
        finiteStateVorticityNegativeOneMass modes tangent := by
  let multiplier : ℝ :=
    (2 * Real.pi) ^ 2 * (receipt.selectedShellSq : ℝ)
  have multiplierPos : 0 < multiplier := by
    exact mul_pos
      (sq_pos_of_pos (by positivity))
      (generatedIntegerShellReceipt_selectedShellSq_cast_pos receipt)
  have supportToProduct :
      receiptSupportTangentEnergy receipt tangent ≤
        ∑ index ∈
            receipt.wholeShellModes ×ˢ
              (Finset.univ : Finset Coordinate),
          Complex.normSq (tangent index.1 index.2) := by
    unfold receiptSupportTangentEnergy
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (receiptSupport_subset_wholeShell_product receipt)
        (fun index indexMem indexNotMem =>
          Complex.normSq_nonneg _)
  have productToRows :
      (∑ index ∈
          receipt.wholeShellModes ×ˢ
            (Finset.univ : Finset Coordinate),
        Complex.normSq (tangent index.1 index.2)) ≤
      ∑ wave ∈ receipt.wholeShellModes,
        3 * ‖tangent wave‖ ^ 2 := by
    calc
      (∑ index ∈
          receipt.wholeShellModes ×ˢ
            (Finset.univ : Finset Coordinate),
        Complex.normSq (tangent index.1 index.2)) =
          ∑ wave ∈ receipt.wholeShellModes,
            ∑ coordinate : Coordinate,
              Complex.normSq (tangent wave coordinate) := by
        exact
          Finset.sum_product'
            receipt.wholeShellModes
            (Finset.univ : Finset Coordinate)
            (fun wave coordinate =>
              Complex.normSq (tangent wave coordinate))
      _ ≤
          ∑ wave ∈ receipt.wholeShellModes,
            3 * ‖tangent wave‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro wave waveMem
        exact
          complexCoordinateAmplitudeSq_le_three_mul_norm_sq
            (tangent wave)
  have densitySumLe :
      (∑ wave ∈ receipt.wholeShellModes,
          ‖tangent wave‖ ^ 2 /
            integerWaveViscousMultiplier wave) ≤
        finiteStateVorticityNegativeOneMass modes tangent := by
    unfold finiteStateVorticityNegativeOneMass
    calc
      (∑ wave ∈ receipt.wholeShellModes,
          ‖tangent wave‖ ^ 2 /
            integerWaveViscousMultiplier wave) =
        ∑ wave ∈ receipt.wholeShellModes,
          if wave = 0 then 0
          else
            ‖tangent wave‖ ^ 2 /
              integerWaveViscousMultiplier wave := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [if_neg (receiptWave_ne_zero receipt waveMem)]
      _ ≤
        ∑ output ∈ modes,
          if output = 0 then 0
          else
            ‖tangent output‖ ^ 2 /
              integerWaveViscousMultiplier output := by
        apply
          Finset.sum_le_sum_of_subset_of_nonneg
            wholeShellSubset
        intro output outputMem outputNotMem
        by_cases outputZero : output = 0
        · simp [outputZero]
        · rw [if_neg outputZero]
          exact
            div_nonneg (sq_nonneg _)
              (mul_nonneg (sq_nonneg _)
                (integerWaveNormSq_nonneg output))
  have rowSumLe :
      (∑ wave ∈ receipt.wholeShellModes,
        ‖tangent wave‖ ^ 2) ≤
          multiplier *
            finiteStateVorticityNegativeOneMass modes tangent := by
    calc
      (∑ wave ∈ receipt.wholeShellModes,
          ‖tangent wave‖ ^ 2) =
        ∑ wave ∈ receipt.wholeShellModes,
          multiplier *
            (‖tangent wave‖ ^ 2 /
              integerWaveViscousMultiplier wave) := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [receiptWave_multiplier receipt waveMem]
        change
          ‖tangent wave‖ ^ 2 =
            multiplier *
              (‖tangent wave‖ ^ 2 / multiplier)
        field_simp [ne_of_gt multiplierPos]
      _ =
        multiplier *
          (∑ wave ∈ receipt.wholeShellModes,
            ‖tangent wave‖ ^ 2 /
              integerWaveViscousMultiplier wave) := by
        rw [Finset.mul_sum]
      _ ≤
        multiplier *
          finiteStateVorticityNegativeOneMass modes tangent :=
        mul_le_mul_of_nonneg_left densitySumLe multiplierPos.le
  calc
    receiptSupportTangentEnergy receipt tangent ≤
        ∑ index ∈
            receipt.wholeShellModes ×ˢ
              (Finset.univ : Finset Coordinate),
          Complex.normSq (tangent index.1 index.2) :=
      supportToProduct
    _ ≤
        ∑ wave ∈ receipt.wholeShellModes,
          3 * ‖tangent wave‖ ^ 2 :=
      productToRows
    _ =
        3 *
          (∑ wave ∈ receipt.wholeShellModes,
            ‖tangent wave‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤
        3 *
          (multiplier *
            finiteStateVorticityNegativeOneMass modes tangent) :=
      mul_le_mul_of_nonneg_left rowSumLe (by norm_num)
    _ =
      3 * (2 * Real.pi) ^ 2 *
          (receipt.selectedShellSq : ℝ) *
        finiteStateVorticityNegativeOneMass modes tangent := by
      dsimp [multiplier]
      ring

/-! ## Time Cauchy--Schwarz on the whole flattened receipt support -/

private theorem norm_intervalIntegral_sq_le_length_mul_integral_norm_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : ℝ → E)
    (a b : ℝ)
    (hab : a ≤ b)
    (fContinuous : ContinuousOn f (Icc a b)) :
    ‖∫ t in a..b, f t‖ ^ 2 ≤
      (b - a) * ∫ t in a..b, ‖f t‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have normContinuous :
      ContinuousOn (fun t => ‖f t‖) (Icc a b) :=
    fContinuous.norm
  have normSqContinuous :
      ContinuousOn (fun t => ‖f t‖ ^ 2) (Icc a b) :=
    normContinuous.pow 2
  have normSqIntegrable :
      Integrable (fun t => ‖f t‖ ^ 2) μ := by
    change IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc a b)
    exact
      normSqContinuous.integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  have normIntegrable :
      Integrable (fun t => ‖f t‖) μ := by
    change IntegrableOn (fun t => ‖f t‖) (Ioc a b)
    exact
      normContinuous.integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  have normMemLpNat :
      MemLp (fun t => ‖f t‖) 2 μ :=
    (memLp_two_iff_integrable_sq
      normIntegrable.aestronglyMeasurable).mpr normSqIntegrable
  have normMemLp :
      MemLp (fun t => ‖f t‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using normMemLpNat
  have oneMemLp :
      MemLp (fun _ : ℝ => (1 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) μ :=
    memLp_const 1
  have cauchy :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (μ := μ)
      (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t => ‖f t‖)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      (Filter.Eventually.of_forall fun t => norm_nonneg (f t))
      oneMemLp normMemLp
  have measureReal : μ.real univ = b - a := by
    dsimp [μ]
    rw [
      measureReal_def,
      Measure.restrict_apply_univ,
      Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have cauchySqrt :
      ∫ t, ‖f t‖ ∂μ ≤
        Real.sqrt (b - a) *
          Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂μ) := by
    norm_num [measureReal, Real.sqrt_eq_rpow] at cauchy ⊢
    exact cauchy
  rw [
    intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  change
    ‖∫ t, f t ∂μ‖ ^ 2 ≤
      (b - a) * ∫ t, ‖f t‖ ^ 2 ∂μ
  have normIntegralLe :
      ‖∫ t, f t ∂μ‖ ≤ ∫ t, ‖f t‖ ∂μ :=
    norm_integral_le_integral_norm _
  have rhsSqrtNonneg :
      0 ≤
        Real.sqrt (b - a) *
          Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have chained :
      ‖∫ t, f t ∂μ‖ ≤
        Real.sqrt (b - a) *
          Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂μ) :=
    normIntegralLe.trans cauchySqrt
  have squared :=
    (sq_le_sq₀ (norm_nonneg _) rhsSqrtNonneg).mpr chained
  rw [
    mul_pow,
    Real.sq_sqrt (sub_nonneg.mpr hab),
    Real.sq_sqrt
      (integral_nonneg fun t => sq_nonneg ‖f t‖)] at squared
  exact squared

private theorem finiteGalerkinGeneratorCoordinate_continuousOn
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (index : IntegerShellCoefficientCoordinate)
    (a b : ℝ)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    ContinuousOn
      (fun t =>
        finiteStateVorticityGenerator
          modes ν (trajectory t) index.1 index.2)
      (Icc a b) := by
  intro t tMem
  have rowContinuous :
      ContinuousAt
        (fun time =>
          finiteStateVorticityGenerator
            modes ν (trajectory time) index.1) t := by
    exact
      (((complexVorticityEvaluation_contDiff index.1).continuous.comp
        (finiteStateVorticityGenerator_contDiff
          modes ν).continuous).continuousAt.comp
            (evolves t tMem).continuousAt)
  exact
    ((continuous_apply index.2).continuousAt.comp
      rowContinuous).continuousWithinAt

private theorem finiteGalerkinCoordinate_timeIncrement_normSq_le
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (index : IntegerShellCoefficientCoordinate)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    Complex.normSq
        (trajectory b index.1 index.2 -
          trajectory a index.1 index.2) ≤
      (b - a) *
        ∫ t in a..b,
          Complex.normSq
            (finiteStateVorticityGenerator
              modes ν (trajectory t) index.1 index.2) := by
  let tangentCoordinate : ℝ → ℂ :=
    fun t =>
      finiteStateVorticityGenerator
        modes ν (trajectory t) index.1 index.2
  have tangentCoordinateContinuous :
      ContinuousOn tangentCoordinate (Icc a b) :=
    finiteGalerkinGeneratorCoordinate_continuousOn
      modes ν trajectory index a b evolves
  have tangentCoordinateIntegrable :
      IntervalIntegrable tangentCoordinate volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc
      hab tangentCoordinateContinuous
  have coordinateFTC :
      (∫ t in a..b, tangentCoordinate t) =
        trajectory b index.1 index.2 -
          trajectory a index.1 index.2 := by
    apply
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => trajectory t index.1 index.2)
        (f' := tangentCoordinate)
    · intro t tMem
      have rowDerivative :=
        complexVorticityTrajectoryWave_hasDerivAt
          trajectory t
          (finiteStateVorticityGenerator
            modes ν (trajectory t))
          index.1
          (evolves t (by rwa [uIcc_of_le hab] at tMem))
      simpa [tangentCoordinate] using
        ((hasDerivAt_const t
          (ContinuousLinearMap.proj index.2)).clm_apply
            rowDerivative)
    · exact tangentCoordinateIntegrable
  have cauchy :=
    norm_intervalIntegral_sq_le_length_mul_integral_norm_sq
      tangentCoordinate a b hab tangentCoordinateContinuous
  rw [coordinateFTC] at cauchy
  simpa [Complex.normSq_eq_norm_sq, tangentCoordinate] using cauchy

/-- Time Cauchy--Schwarz is summed over the complete flattened receipt support
before any global negative-one estimate is applied. -/
theorem receiptSupportDifferenceEnergy_le_length_mul_integral_tangentEnergy
    (modes : Finset IntegerWavevector)
    (receipt : GeneratedIntegerShellReceipt)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    receiptSupportDifferenceEnergy receipt
        (trajectory b) (trajectory a) ≤
      (b - a) *
        ∫ t in a..b,
          receiptSupportTangentEnergy receipt
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) := by
  have coordinateIntegrable :
      ∀ index ∈
          (generatedIntegerShellReceiptTrace receipt).support,
        IntervalIntegrable
          (fun t =>
            Complex.normSq
              (finiteStateVorticityGenerator
                modes ν (trajectory t) index.1 index.2))
          volume a b := by
    intro index indexMem
    exact
      ContinuousOn.intervalIntegrable_of_Icc hab
        (by
          simpa [Function.comp_def] using
            Complex.continuous_normSq.comp_continuousOn
              (finiteGalerkinGeneratorCoordinate_continuousOn
                modes ν trajectory index a b evolves))
  unfold receiptSupportDifferenceEnergy receiptSupportTangentEnergy
  calc
    (∑ index ∈
        (generatedIntegerShellReceiptTrace receipt).support,
      Complex.normSq
        (trajectory b index.1 index.2 -
          trajectory a index.1 index.2)) ≤
      ∑ index ∈
          (generatedIntegerShellReceiptTrace receipt).support,
        (b - a) *
          ∫ t in a..b,
            Complex.normSq
              (finiteStateVorticityGenerator
                modes ν (trajectory t) index.1 index.2) := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact
        finiteGalerkinCoordinate_timeIncrement_normSq_le
          modes ν trajectory index a b hab evolves
    _ =
      (b - a) *
        ∫ t in a..b,
          ∑ index ∈
            (generatedIntegerShellReceiptTrace receipt).support,
            Complex.normSq
              (finiteStateVorticityGenerator
                modes ν (trajectory t) index.1 index.2) := by
      rw [← Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum coordinateIntegrable]

/-! ## Frequency-cancelled whole-receipt increment -/

private theorem receiptSupportTangentEnergy_continuousOn
    (modes : Finset IntegerWavevector)
    (receipt : GeneratedIntegerShellReceipt)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    ContinuousOn
      (fun t =>
        receiptSupportTangentEnergy receipt
          (finiteStateVorticityGenerator
            modes ν (trajectory t)))
      (Icc a b) := by
  unfold receiptSupportTangentEnergy
  apply continuousOn_finsetSum
  intro index indexMem
  simpa [Function.comp_def] using
    Complex.continuous_normSq.comp_continuousOn
      (finiteGalerkinGeneratorCoordinate_continuousOn
        modes ν trajectory index a b evolves)

/-- The exact whole-receipt increment consumes one selected-shell frequency
factor and the actual row-weighted `L²_t H⁻¹` tangent mass.  All supported
coordinates are summed before the negative norm is read, so the constant is
independent of both shell cardinality and Galerkin cutoff. -/
theorem
    receiptSupportDifferenceEnergy_le_three_length_shell_integral_negativeOneMass
    (modes : Finset IntegerWavevector)
    (receipt : GeneratedIntegerShellReceipt)
    (wholeShellSubset : receipt.wholeShellModes ⊆ modes)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    receiptSupportDifferenceEnergy receipt
        (trajectory b) (trajectory a) ≤
      3 * (b - a) * (2 * Real.pi) ^ 2 *
          (receipt.selectedShellSq : ℝ) *
        ∫ t in a..b,
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) := by
  let scale : ℝ :=
    3 * (2 * Real.pi) ^ 2 *
      (receipt.selectedShellSq : ℝ)
  have tangentContinuous :
      ContinuousOn
        (fun t =>
          receiptSupportTangentEnergy receipt
            (finiteStateVorticityGenerator
              modes ν (trajectory t)))
        (Icc a b) :=
    receiptSupportTangentEnergy_continuousOn
      modes receipt ν trajectory a b evolves
  have massContinuous :
      ContinuousOn
        (fun t =>
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν (trajectory t)))
        (Icc a b) :=
    finiteGalerkinGeneratorNegativeOneMass_continuousOn
      modes ν trajectory a b evolves
  have tangentIntegrable :
      IntervalIntegrable
        (fun t =>
          receiptSupportTangentEnergy receipt
            (finiteStateVorticityGenerator
              modes ν (trajectory t)))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab tangentContinuous
  have massIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν (trajectory t)))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab massContinuous
  have scaledMassIntegrable :
      IntervalIntegrable
        (fun t =>
          scale *
            finiteStateVorticityNegativeOneMass modes
              (finiteStateVorticityGenerator
                modes ν (trajectory t)))
        volume a b :=
    massIntegrable.const_mul scale
  have pointwise :
      ∀ t ∈ Icc a b,
        receiptSupportTangentEnergy receipt
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) ≤
          scale *
            finiteStateVorticityNegativeOneMass modes
              (finiteStateVorticityGenerator
                modes ν (trajectory t)) := by
    intro t tMem
    simpa [scale] using
      receiptSupportTangentEnergy_le_three_shell_negativeOneMass
        modes receipt wholeShellSubset
        (finiteStateVorticityGenerator
          modes ν (trajectory t))
  have integratedTangentLe :
      (∫ t in a..b,
        receiptSupportTangentEnergy receipt
          (finiteStateVorticityGenerator
            modes ν (trajectory t))) ≤
        ∫ t in a..b,
          scale *
            finiteStateVorticityNegativeOneMass modes
              (finiteStateVorticityGenerator
                modes ν (trajectory t)) :=
    intervalIntegral.integral_mono_on
      hab tangentIntegrable scaledMassIntegrable pointwise
  calc
    receiptSupportDifferenceEnergy receipt
        (trajectory b) (trajectory a) ≤
      (b - a) *
        ∫ t in a..b,
          receiptSupportTangentEnergy receipt
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) :=
      receiptSupportDifferenceEnergy_le_length_mul_integral_tangentEnergy
        modes receipt ν trajectory a b hab evolves
    _ ≤
      (b - a) *
        ∫ t in a..b,
          scale *
            finiteStateVorticityNegativeOneMass modes
              (finiteStateVorticityGenerator
                modes ν (trajectory t)) :=
      mul_le_mul_of_nonneg_left integratedTangentLe
        (sub_nonneg.mpr hab)
    _ =
      3 * (b - a) * (2 * Real.pi) ^ 2 *
          (receipt.selectedShellSq : ℝ) *
        ∫ t in a..b,
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) := by
      rw [intervalIntegral.integral_const_mul]
      dsimp [scale]
      ring

end

end ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistenceCost
end NavierStokes
end SaturationMonoid
