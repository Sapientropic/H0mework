import H0mework.NavierStokes.Fourier.FixedOutputNonlinearContinuity

/-!
# Finite-carrier negative-one control of nonlinear differences

This module keeps the two velocity--vorticity placements in the actual
bilinear Fourier row until after summing over every output.  Discrete Young
convolution then gives a cutoff-independent finite estimate with the two
terms required by a difference-energy argument:

```text
M(right)² * mass(left) + M(left)² * mass(right).
```

Applying the exact polarization of `N(left) - N(right)` therefore retains
both the ambient-velocity cost multiplying the difference mass and the
difference-velocity cost multiplying the ambient masses.  No fixed-output
bound is summed over the lattice, and no mode-count or terminal-frequency
parameter enters the estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteNonlinearDifferenceNegativeOne

open scoped BigOperators ENNReal Topology

open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity

noncomputable section

/-! ## Mixed finite convolution -/

/-- The actual finite velocity--vorticity convolution with the velocity
amplitude in the first frequency slot. -/
def finiteStateVelocityVorticityConvolutionAmplitude
    (modes : Finset IntegerWavevector)
    (velocityState vorticityState : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ℝ :=
  ∑ first ∈ modes,
    if output - first ∈ modes then
      velocityRowAmplitude velocityState first *
        vorticityRowAmplitude vorticityState (output - first)
    else 0

theorem finiteStateVelocityVorticityConvolutionAmplitude_nonneg
    (modes : Finset IntegerWavevector)
    (velocityState vorticityState : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    0 ≤
      finiteStateVelocityVorticityConvolutionAmplitude
        modes velocityState vorticityState output := by
  unfold finiteStateVelocityVorticityConvolutionAmplitude
  exact Finset.sum_nonneg fun first firstMem => by
    split_ifs
    · exact mul_nonneg
        (velocityRowAmplitude_nonneg velocityState first)
        (vorticityRowAmplitude_nonneg
          vorticityState (output - first))
    · exact le_rfl

private theorem doubleIncidenceVelocityVorticity_eq
    (modes : Finset IntegerWavevector)
    (velocityState vorticityState : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ modes,
        ∑ second ∈ modes,
          if first + second = output then
            velocityRowAmplitude velocityState first *
              vorticityRowAmplitude vorticityState second
          else 0) =
      finiteStateVelocityVorticityConvolutionAmplitude
        modes velocityState vorticityState output := by
  unfold finiteStateVelocityVorticityConvolutionAmplitude
  apply Finset.sum_congr rfl
  intro first firstMem
  have condition :
      ∀ second : IntegerWavevector,
        first + second = output ↔
          second = output - first := by
    intro second
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [condition]
  by_cases translatedMem : output - first ∈ modes
  · simp [translatedMem]
  · simp [translatedMem]

/-- The bilinear row keeps both velocity placements before the
Biot--Savart factor is discarded. -/
theorem finiteStateVorticityBilinearCoefficientAt_norm_le_velocityConvolution
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (output : IntegerWavevector) :
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        (finiteStateVelocityVorticityConvolutionAmplitude
            modes right left output +
          finiteStateVelocityVorticityConvolutionAmplitude
            modes left right output) := by
  let angular : ℝ :=
    (2 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  let stretchingScalar : ℝ :=
    ∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          vorticityRowAmplitude left first *
            velocityRowAmplitude right second
        else 0
  let advectionScalar : ℝ :=
    ∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          velocityRowAmplitude left first *
            vorticityRowAmplitude right second
        else 0
  have aggregateNorm :
      ‖finiteStateVorticityBilinearCoefficientAt
          modes left right output‖ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityBilinearPairContribution
                  left right (first, second)
              else 0‖ := by
    unfold finiteStateVorticityBilinearCoefficientAt
    exact
      (norm_sum_le modes fun first =>
        ∑ second ∈ modes,
          if first + second = output then
            finiteStateVorticityBilinearPairContribution
              left right (first, second)
          else 0).trans
        (Finset.sum_le_sum fun first firstMem =>
          norm_sum_le modes fun second =>
            if first + second = output then
              finiteStateVorticityBilinearPairContribution
                left right (first, second)
            else 0)
  have pairwiseNorm :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityBilinearPairContribution
                  left right (first, second)
              else 0‖) ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityRowAmplitude left first *
                    velocityRowAmplitude right second +
                  velocityRowAmplitude left first *
                    vorticityRowAmplitude right second)
            else 0 := by
    apply Finset.sum_le_sum
    intro first firstMem
    apply Finset.sum_le_sum
    intro second secondMem
    by_cases incidence : first + second = output
    · simp only [if_pos incidence]
      exact
        finiteStateVorticityBilinearPairContribution_norm_le_preBiotSavart
          left right output first second incidence
            (leftTransverse first firstMem)
    · simp [incidence]
  have scalarSplit :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityRowAmplitude left first *
                    velocityRowAmplitude right second +
                  velocityRowAmplitude left first *
                    vorticityRowAmplitude right second)
            else 0) =
        angular * stretchingScalar +
          angular * advectionScalar := by
    simp only [stretchingScalar, advectionScalar]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro first firstMem
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases incidence : first + second = output <;>
      simp [incidence, mul_add]
  have stretchingEq :
      stretchingScalar =
        finiteStateVelocityVorticityConvolutionAmplitude
          modes right left output := by
    dsimp [stretchingScalar]
    rw [Finset.sum_comm]
    simpa only [add_comm, mul_comm] using
      doubleIncidenceVelocityVorticity_eq
        modes right left output
  have advectionEq :
      advectionScalar =
        finiteStateVelocityVorticityConvolutionAmplitude
          modes left right output := by
    exact
      doubleIncidenceVelocityVorticity_eq
        modes left right output
  calc
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityBilinearPairContribution
                  left right (first, second)
              else 0‖ :=
      aggregateNorm
    _ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityRowAmplitude left first *
                    velocityRowAmplitude right second +
                  velocityRowAmplitude left first *
                    vorticityRowAmplitude right second)
            else 0 :=
      pairwiseNorm
    _ = angular * stretchingScalar +
          angular * advectionScalar :=
      scalarSplit
    _ =
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (finiteStateVelocityVorticityConvolutionAmplitude
              modes right left output +
            finiteStateVelocityVorticityConvolutionAmplitude
              modes left right output) := by
      rw [stretchingEq, advectionEq]
      dsimp [angular]
      ring

private theorem translatedVorticityAmplitudeSq_sum_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (first : IntegerWavevector) :
    (∑ output ∈ modes,
        if output - first ∈ modes then
          vorticityRowAmplitude state (output - first) ^ 2
        else 0) ≤
      ∑ second ∈ modes,
        vorticityRowAmplitude state second ^ 2 := by
  let translated : Finset IntegerWavevector :=
    modes.image fun second => first + second
  have filteredSubset :
      modes.filter (fun output => output - first ∈ modes) ⊆
        translated := by
    intro output outputMem
    have membership := Finset.mem_filter.mp outputMem
    apply Finset.mem_image.mpr
    refine ⟨output - first, membership.2, ?_⟩
    abel
  have translatedSum :
      (∑ output ∈ translated,
          vorticityRowAmplitude state (output - first) ^ 2) =
        ∑ second ∈ modes,
          vorticityRowAmplitude state second ^ 2 := by
    dsimp [translated]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro second secondMem
      congr 2
      abel
    · intro left leftMem right rightMem equality
      exact add_left_cancel equality
  rw [← Finset.sum_filter]
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg
      filteredSubset
      (fun output outputMem outputNotMem =>
        sq_nonneg
          (vorticityRowAmplitude state (output - first)))).trans_eq
      translatedSum

/-- Mixed discrete `ℓ¹ * ℓ² → ℓ²` Young inequality on the actual finite
velocity--vorticity convolution. -/
theorem sum_velocityVorticityConvolutionAmplitude_sq_le
    (modes : Finset IntegerWavevector)
    (velocityState vorticityState : ComplexVorticityHilbertState) :
    (∑ output ∈ modes,
        finiteStateVelocityVorticityConvolutionAmplitude
          modes velocityState vorticityState output ^ 2) ≤
      (∑ first ∈ modes,
          velocityRowAmplitude velocityState first) ^ 2 *
        ∑ second ∈ modes,
          vorticityRowAmplitude vorticityState second ^ 2 := by
  let velocitySum : ℝ :=
    ∑ first ∈ modes, velocityRowAmplitude velocityState first
  let vorticitySqSum : ℝ :=
    ∑ second ∈ modes, vorticityRowAmplitude vorticityState second ^ 2
  let weightedTranslate :
      IntegerWavevector → IntegerWavevector → ℝ :=
    fun output first =>
      if output - first ∈ modes then
        velocityRowAmplitude velocityState first *
          vorticityRowAmplitude vorticityState (output - first) ^ 2
      else 0
  have velocitySumNonneg : 0 ≤ velocitySum := by
    exact Finset.sum_nonneg fun first firstMem =>
      velocityRowAmplitude_nonneg velocityState first
  have pointwise :
      ∀ output ∈ modes,
        finiteStateVelocityVorticityConvolutionAmplitude
            modes velocityState vorticityState output ^ 2 ≤
          velocitySum *
            ∑ first ∈ modes,
              weightedTranslate output first := by
    intro output outputMem
    unfold finiteStateVelocityVorticityConvolutionAmplitude
    have cauchy :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        modes
        (r := fun first =>
          if output - first ∈ modes then
            velocityRowAmplitude velocityState first *
              vorticityRowAmplitude
                vorticityState (output - first)
          else 0)
        (f := fun first =>
          velocityRowAmplitude velocityState first)
        (g := fun first => weightedTranslate output first)
        (fun first firstMem =>
          velocityRowAmplitude_nonneg velocityState first)
        (fun first firstMem => by
          dsimp [weightedTranslate]
          split_ifs
          · exact mul_nonneg
              (velocityRowAmplitude_nonneg velocityState first)
              (sq_nonneg _)
          · exact le_rfl)
        (fun first firstMem => by
          dsimp [weightedTranslate]
          by_cases translatedMem : output - first ∈ modes
          · simp only [if_pos translatedMem]
            exact le_of_eq (by ring)
          · simp [translatedMem])
    simpa only [velocitySum] using cauchy
  have weightedTotalLe :
      (∑ output ∈ modes,
          ∑ first ∈ modes,
            weightedTranslate output first) ≤
        velocitySum * vorticitySqSum := by
    rw [Finset.sum_comm]
    calc
      (∑ first ∈ modes,
          ∑ output ∈ modes,
            weightedTranslate output first) ≤
          ∑ first ∈ modes,
            velocityRowAmplitude velocityState first *
              vorticitySqSum := by
        apply Finset.sum_le_sum
        intro first firstMem
        dsimp [weightedTranslate]
        have factorEq :
            (∑ output ∈ modes,
                if output - first ∈ modes then
                  velocityRowAmplitude velocityState first *
                    vorticityRowAmplitude
                      vorticityState (output - first) ^ 2
                else 0) =
              velocityRowAmplitude velocityState first *
                ∑ output ∈ modes,
                  if output - first ∈ modes then
                    vorticityRowAmplitude
                      vorticityState (output - first) ^ 2
                  else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro output outputMem
          by_cases translatedMem : output - first ∈ modes <;>
            simp [translatedMem]
        rw [factorEq]
        exact
          mul_le_mul_of_nonneg_left
            (translatedVorticityAmplitudeSq_sum_le
              modes vorticityState first)
            (velocityRowAmplitude_nonneg velocityState first)
      _ = velocitySum * vorticitySqSum := by
        rw [Finset.sum_mul]
  calc
    (∑ output ∈ modes,
        finiteStateVelocityVorticityConvolutionAmplitude
          modes velocityState vorticityState output ^ 2) ≤
        ∑ output ∈ modes,
          velocitySum *
            ∑ first ∈ modes,
              weightedTranslate output first :=
      Finset.sum_le_sum pointwise
    _ =
        velocitySum *
          (∑ output ∈ modes,
            ∑ first ∈ modes,
              weightedTranslate output first) := by
      rw [Finset.mul_sum]
    _ ≤ velocitySum * (velocitySum * vorticitySqSum) :=
      mul_le_mul_of_nonneg_left weightedTotalLe velocitySumNonneg
    _ =
        (∑ first ∈ modes,
            velocityRowAmplitude velocityState first) ^ 2 *
          ∑ second ∈ modes,
            vorticityRowAmplitude vorticityState second ^ 2 := by
      dsimp [velocitySum, vorticitySqSum]
      ring

private theorem vorticityRowAmplitude_sq_sum_eq_enstrophy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
        vorticityRowAmplitude state wave ^ 2) =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact vorticityRowAmplitude_sq state wave

/-! ## Finite negative-one bilinear and difference estimates -/

/-- Negative-one mass of the actual finite bilinear row. -/
def finiteStateVorticityBilinearNegativeOneMass
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ modes,
    if output = 0 then 0
    else
      ‖finiteStateVorticityBilinearCoefficientAt
          modes left right output‖ ^ 2 /
        integerWaveViscousMultiplier output

private theorem bilinearNegativeOneRow_le_convolutions
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ^ 2 /
        integerWaveViscousMultiplier output ≤
      (finiteStateVelocityVorticityConvolutionAmplitude
          modes right left output +
        finiteStateVelocityVorticityConvolutionAmplitude
          modes left right output) ^ 2 := by
  let convolution :=
    finiteStateVelocityVorticityConvolutionAmplitude
        modes right left output +
      finiteStateVelocityVorticityConvolutionAmplitude
        modes left right output
  have convolutionNonneg : 0 ≤ convolution :=
    add_nonneg
      (finiteStateVelocityVorticityConvolutionAmplitude_nonneg
        modes right left output)
      (finiteStateVelocityVorticityConvolutionAmplitude_nonneg
        modes left right output)
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          convolution := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.sqrt_nonneg _))
      convolutionNonneg
  have normLe :
      ‖finiteStateVorticityBilinearCoefficientAt
          modes left right output‖ ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          convolution := by
    simpa [convolution] using
      finiteStateVorticityBilinearCoefficientAt_norm_le_velocityConvolution
        modes left right leftTransverse output
  have normSqLe :
      ‖finiteStateVorticityBilinearCoefficientAt
          modes left right output‖ ^ 2 ≤
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          convolution) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mpr normLe
  have multiplierPos :
      0 < integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_pos
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
      (integerWaveNormSq_pos outputNe)
  calc
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ^ 2 /
        integerWaveViscousMultiplier output ≤
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          convolution) ^ 2 /
          integerWaveViscousMultiplier output :=
      div_le_div_of_nonneg_right normSqLe multiplierPos.le
    _ = convolution ^ 2 := by
      unfold integerWaveViscousMultiplier
      rw [show
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            convolution) ^ 2 =
          (2 * Real.pi) ^ 2 *
            Real.sqrt (integerWaveNormSq output) ^ 2 *
            convolution ^ 2 by ring]
      rw [Real.sq_sqrt (integerWaveNormSq_nonneg output)]
      field_simp [Real.pi_ne_zero,
        integerWaveNormSq_ne_zero outputNe]

/-- Cutoff-independent `H⁻¹` estimate for an actual finite bilinear row.
Both velocity placements remain visible in the conclusion. -/
theorem finiteStateVorticityBilinearNegativeOneMass_le
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left) :
    finiteStateVorticityBilinearNegativeOneMass
        modes left right ≤
      2 *
        (finiteStateVelocityMajorant modes right ^ 2 *
            finiteStateVorticityCoefficientEnstrophy modes left +
          finiteStateVelocityMajorant modes left ^ 2 *
            finiteStateVorticityCoefficientEnstrophy modes right) := by
  have rowSumLe :
      finiteStateVorticityBilinearNegativeOneMass
          modes left right ≤
        ∑ output ∈ modes,
          (finiteStateVelocityVorticityConvolutionAmplitude
              modes right left output +
            finiteStateVelocityVorticityConvolutionAmplitude
              modes left right output) ^ 2 := by
    unfold finiteStateVorticityBilinearNegativeOneMass
    apply Finset.sum_le_sum
    intro output outputMem
    by_cases outputZero : output = 0
    · rw [if_pos outputZero]
      exact sq_nonneg _
    · rw [if_neg outputZero]
      exact
        bilinearNegativeOneRow_le_convolutions
          modes left right leftTransverse output outputZero
  have splitSquares :
      (∑ output ∈ modes,
          (finiteStateVelocityVorticityConvolutionAmplitude
              modes right left output +
            finiteStateVelocityVorticityConvolutionAmplitude
              modes left right output) ^ 2) ≤
        2 *
          ((∑ output ∈ modes,
              finiteStateVelocityVorticityConvolutionAmplitude
                modes right left output ^ 2) +
            ∑ output ∈ modes,
              finiteStateVelocityVorticityConvolutionAmplitude
                modes left right output ^ 2) := by
    calc
      (∑ output ∈ modes,
          (finiteStateVelocityVorticityConvolutionAmplitude
              modes right left output +
            finiteStateVelocityVorticityConvolutionAmplitude
              modes left right output) ^ 2) ≤
          ∑ output ∈ modes,
            2 *
              (finiteStateVelocityVorticityConvolutionAmplitude
                  modes right left output ^ 2 +
                finiteStateVelocityVorticityConvolutionAmplitude
                  modes left right output ^ 2) := by
        apply Finset.sum_le_sum
        intro output outputMem
        nlinarith [
          sq_nonneg
            (finiteStateVelocityVorticityConvolutionAmplitude
                modes right left output -
              finiteStateVelocityVorticityConvolutionAmplitude
                modes left right output)]
      _ =
          2 *
            ((∑ output ∈ modes,
                finiteStateVelocityVorticityConvolutionAmplitude
                  modes right left output ^ 2) +
              ∑ output ∈ modes,
                finiteStateVelocityVorticityConvolutionAmplitude
                  modes left right output ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have reverseYoung :=
    sum_velocityVorticityConvolutionAmplitude_sq_le
      modes right left
  have forwardYoung :=
    sum_velocityVorticityConvolutionAmplitude_sq_le
      modes left right
  calc
    finiteStateVorticityBilinearNegativeOneMass
        modes left right ≤
        ∑ output ∈ modes,
          (finiteStateVelocityVorticityConvolutionAmplitude
              modes right left output +
            finiteStateVelocityVorticityConvolutionAmplitude
              modes left right output) ^ 2 :=
      rowSumLe
    _ ≤
        2 *
          ((∑ output ∈ modes,
              finiteStateVelocityVorticityConvolutionAmplitude
                modes right left output ^ 2) +
            ∑ output ∈ modes,
              finiteStateVelocityVorticityConvolutionAmplitude
                modes left right output ^ 2) :=
      splitSquares
    _ ≤
        2 *
          (((∑ first ∈ modes,
                velocityRowAmplitude right first) ^ 2 *
              ∑ second ∈ modes,
                vorticityRowAmplitude left second ^ 2) +
            (∑ first ∈ modes,
                velocityRowAmplitude left first) ^ 2 *
              ∑ second ∈ modes,
                vorticityRowAmplitude right second ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add reverseYoung forwardYoung) (by norm_num)
    _ =
        2 *
          (finiteStateVelocityMajorant modes right ^ 2 *
              finiteStateVorticityCoefficientEnstrophy modes left +
            finiteStateVelocityMajorant modes left ^ 2 *
              finiteStateVorticityCoefficientEnstrophy modes right) := by
      rw [vorticityRowAmplitude_sq_sum_eq_enstrophy,
        vorticityRowAmplitude_sq_sum_eq_enstrophy]
      rfl

/-- Negative-one mass of the actual finite nonlinear difference row. -/
def finiteStateVorticityNonlinearDifferenceNegativeOneMass
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ modes,
    if output = 0 then 0
    else
      ‖finiteStateVorticityNonlinearCoefficientAt modes left output -
          finiteStateVorticityNonlinearCoefficientAt modes right output‖ ^ 2 /
        integerWaveViscousMultiplier output

/-- The finite nonlinear difference has the two-term `H⁻¹` bound needed by
the difference-energy method.  In particular, the difference-velocity term
is retained rather than replaced by an ambient upper bound. -/
theorem finiteStateVorticityNonlinearDifferenceNegativeOneMass_le
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right) :
    finiteStateVorticityNonlinearDifferenceNegativeOneMass
        modes left right ≤
      4 *
        ((finiteStateVelocityMajorant modes left ^ 2 +
            finiteStateVelocityMajorant modes right ^ 2) *
            finiteStateVorticityCoefficientEnstrophy
              modes (left - right) +
          finiteStateVelocityMajorant modes (left - right) ^ 2 *
            (finiteStateVorticityCoefficientEnstrophy modes left +
              finiteStateVorticityCoefficientEnstrophy modes right)) := by
  let difference := left - right
  have differenceTransverse :
      FiniteStateTransverseOn modes difference := by
    exact finiteStateTransverseOn_sub
      modes left right leftTransverse rightTransverse
  have rowSplit :
      finiteStateVorticityNonlinearDifferenceNegativeOneMass
          modes left right ≤
        2 *
          (finiteStateVorticityBilinearNegativeOneMass
              modes difference left +
            finiteStateVorticityBilinearNegativeOneMass
              modes right difference) := by
    unfold finiteStateVorticityNonlinearDifferenceNegativeOneMass
      finiteStateVorticityBilinearNegativeOneMass
    calc
      (∑ output ∈ modes,
          if output = 0 then 0
          else
            ‖finiteStateVorticityNonlinearCoefficientAt modes left output -
                finiteStateVorticityNonlinearCoefficientAt modes right output‖ ^ 2 /
              integerWaveViscousMultiplier output) ≤
          ∑ output ∈ modes,
            2 *
              ((if output = 0 then 0
                else
                  ‖finiteStateVorticityBilinearCoefficientAt
                      modes difference left output‖ ^ 2 /
                    integerWaveViscousMultiplier output) +
                (if output = 0 then 0
                else
                  ‖finiteStateVorticityBilinearCoefficientAt
                      modes right difference output‖ ^ 2 /
                    integerWaveViscousMultiplier output)) := by
        apply Finset.sum_le_sum
        intro output outputMem
        by_cases outputZero : output = 0
        · simp [outputZero]
        · rw [if_neg outputZero, if_neg outputZero, if_neg outputZero]
          rw [finiteStateVorticityNonlinearCoefficientAt_sub]
          have multiplierNonneg :
              0 ≤ integerWaveViscousMultiplier output := by
            unfold integerWaveViscousMultiplier
            exact mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg output)
          have normSquare :
              ‖finiteStateVorticityBilinearCoefficientAt
                    modes difference left output +
                  finiteStateVorticityBilinearCoefficientAt
                    modes right difference output‖ ^ 2 ≤
                2 *
                  (‖finiteStateVorticityBilinearCoefficientAt
                      modes difference left output‖ ^ 2 +
                    ‖finiteStateVorticityBilinearCoefficientAt
                      modes right difference output‖ ^ 2) := by
            calc
              ‖finiteStateVorticityBilinearCoefficientAt
                    modes difference left output +
                  finiteStateVorticityBilinearCoefficientAt
                    modes right difference output‖ ^ 2 ≤
                  (‖finiteStateVorticityBilinearCoefficientAt
                      modes difference left output‖ +
                    ‖finiteStateVorticityBilinearCoefficientAt
                      modes right difference output‖) ^ 2 :=
                (sq_le_sq₀ (norm_nonneg _)
                  (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
                    (norm_add_le _ _)
              _ ≤
                  2 *
                    (‖finiteStateVorticityBilinearCoefficientAt
                        modes difference left output‖ ^ 2 +
                      ‖finiteStateVorticityBilinearCoefficientAt
                        modes right difference output‖ ^ 2) := by
                nlinarith [
                  sq_nonneg
                    (‖finiteStateVorticityBilinearCoefficientAt
                        modes difference left output‖ -
                      ‖finiteStateVorticityBilinearCoefficientAt
                        modes right difference output‖)]
          calc
            ‖finiteStateVorticityBilinearCoefficientAt
                  modes difference left output +
                finiteStateVorticityBilinearCoefficientAt
                  modes right difference output‖ ^ 2 /
                integerWaveViscousMultiplier output ≤
                (2 *
                  (‖finiteStateVorticityBilinearCoefficientAt
                      modes difference left output‖ ^ 2 +
                    ‖finiteStateVorticityBilinearCoefficientAt
                      modes right difference output‖ ^ 2)) /
                  integerWaveViscousMultiplier output :=
              div_le_div_of_nonneg_right normSquare multiplierNonneg
            _ =
                2 *
                  (‖finiteStateVorticityBilinearCoefficientAt
                        modes difference left output‖ ^ 2 /
                      integerWaveViscousMultiplier output +
                    ‖finiteStateVorticityBilinearCoefficientAt
                        modes right difference output‖ ^ 2 /
                      integerWaveViscousMultiplier output) := by
              ring
      _ =
          2 *
            ((∑ output ∈ modes,
                if output = 0 then 0
                else
                  ‖finiteStateVorticityBilinearCoefficientAt
                      modes difference left output‖ ^ 2 /
                    integerWaveViscousMultiplier output) +
              ∑ output ∈ modes,
                if output = 0 then 0
                else
                  ‖finiteStateVorticityBilinearCoefficientAt
                      modes right difference output‖ ^ 2 /
                    integerWaveViscousMultiplier output) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have firstBound :=
    finiteStateVorticityBilinearNegativeOneMass_le
      modes difference left differenceTransverse
  have secondBound :=
    finiteStateVorticityBilinearNegativeOneMass_le
      modes right difference rightTransverse
  calc
    finiteStateVorticityNonlinearDifferenceNegativeOneMass
        modes left right ≤
        2 *
          (finiteStateVorticityBilinearNegativeOneMass
              modes difference left +
            finiteStateVorticityBilinearNegativeOneMass
              modes right difference) :=
      rowSplit
    _ ≤
        2 *
          (2 *
              (finiteStateVelocityMajorant modes left ^ 2 *
                  finiteStateVorticityCoefficientEnstrophy
                    modes difference +
                finiteStateVelocityMajorant modes difference ^ 2 *
                  finiteStateVorticityCoefficientEnstrophy
                    modes left) +
            2 *
              (finiteStateVelocityMajorant modes difference ^ 2 *
                  finiteStateVorticityCoefficientEnstrophy
                    modes right +
                finiteStateVelocityMajorant modes right ^ 2 *
                  finiteStateVorticityCoefficientEnstrophy
                    modes difference)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add firstBound secondBound) (by norm_num)
    _ =
        4 *
          ((finiteStateVelocityMajorant modes left ^ 2 +
              finiteStateVelocityMajorant modes right ^ 2) *
              finiteStateVorticityCoefficientEnstrophy
                modes (left - right) +
            finiteStateVelocityMajorant modes (left - right) ^ 2 *
              (finiteStateVorticityCoefficientEnstrophy modes left +
                finiteStateVorticityCoefficientEnstrophy modes right)) := by
      dsimp [difference]
      ring

end

end ThreeDimensionalVorticityCoefficientFiniteNonlinearDifferenceNegativeOne
end NavierStokes
end SaturationMonoid
