import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow
import H0mework.NavierStokes.Crossing.FrequencySupportExhaustion
import H0mework.NavierStokes.Accumulation.FiniteNormalizedWorkPhaseFace
import H0mework.NavierStokes.Fourier.WholeNonlinearDifferenceNegativeOne
import H0mework.NavierStokes.Crossing.GluingNegativeOneBridge

/-!
# Mixed H⁻¹--H¹ fixed-output rows

The probe first isolates the scalar translated weighted-product mechanism.
It then applies that mechanism to both orderings of one raw fixed-output
vorticity bilinear row.  No whole-action jet or chain rule is constructed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientMixedNegativeOneGradientFixedOutput

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

/-- Inhomogeneous lattice weight.  On zero-free rows it is equivalent to
the homogeneous H±¹ weights already carried by actual receipts. -/
def mixedLatticeWeight (wave : IntegerWavevector) : Real :=
  1 + integerWaveNormSq wave

theorem mixedLatticeWeight_pos (wave : IntegerWavevector) :
    0 < mixedLatticeWeight wave := by
  unfold mixedLatticeWeight
  linarith [integerWaveNormSq_nonneg wave]

def fixedOutputWeightConstant (output : IntegerWavevector) : Real :=
  2 * (integerWaveNormSq output + 1)

theorem fixedOutputWeightConstant_nonneg (output : IntegerWavevector) :
    0 ≤ fixedOutputWeightConstant output := by
  unfold fixedOutputWeightConstant
  nlinarith [integerWaveNormSq_nonneg output]

private theorem integerWaveNormSq_le_two_output_add_translated
    (output first : IntegerWavevector) :
    integerWaveNormSq first ≤
      2 * integerWaveNormSq output +
        2 * integerWaveNormSq (output - first) := by
  unfold integerWaveNormSq
  calc
    (∑ coordinate : Coordinate, (first coordinate : Real) ^ 2) ≤
        ∑ coordinate : Coordinate,
          (2 * (output coordinate : Real) ^ 2 +
            2 * ((output - first) coordinate : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro coordinate _
      have coordinateEq :
          (first coordinate : Real) =
            (output coordinate : Real) -
              ((output - first) coordinate : Real) := by
        simp only [Pi.sub_apply, Int.cast_sub]
        ring
      rw [coordinateEq]
      nlinarith [sq_nonneg
        ((output coordinate : Real) +
          ((output - first) coordinate : Real))]
    _ =
        2 * (∑ coordinate : Coordinate,
          (output coordinate : Real) ^ 2) +
        2 * (∑ coordinate : Coordinate,
          ((output - first) coordinate : Real) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Translation by a fixed output distorts the inhomogeneous lattice weight
by one output-dependent constant only. -/
theorem mixedLatticeWeight_le_fixedOutput_mul_translated
    (output first : IntegerWavevector) :
    mixedLatticeWeight first ≤
      fixedOutputWeightConstant output *
        mixedLatticeWeight (output - first) := by
  have normBound :=
    integerWaveNormSq_le_two_output_add_translated output first
  have outputNonneg := integerWaveNormSq_nonneg output
  have translatedNonneg := integerWaveNormSq_nonneg (output - first)
  unfold mixedLatticeWeight fixedOutputWeightConstant
  nlinarith [mul_nonneg outputNonneg translatedNonneg]

private theorem scalar_weightedYoung
    (output first : IntegerWavevector)
    (left right : Real)
    (_leftNonneg : 0 ≤ left)
    (_rightNonneg : 0 ≤ right) :
    left * right ≤
      (1 / 2 : Real) *
        (left ^ 2 / mixedLatticeWeight first +
          fixedOutputWeightConstant output *
            (mixedLatticeWeight (output - first) * right ^ 2)) := by
  let sourceWeight := mixedLatticeWeight first
  let targetWeight := mixedLatticeWeight (output - first)
  let constant := fixedOutputWeightConstant output
  have sourceWeightPos : 0 < sourceWeight :=
    mixedLatticeWeight_pos first
  have weightComparison : sourceWeight ≤ constant * targetWeight := by
    simpa only [sourceWeight, targetWeight, constant] using
      mixedLatticeWeight_le_fixedOutput_mul_translated output first
  have rightSqNonneg : 0 ≤ right ^ 2 := sq_nonneg right
  have weightedRight :
      sourceWeight * right ^ 2 ≤
        constant * (targetWeight * right ^ 2) := by
    calc
      sourceWeight * right ^ 2 ≤
          (constant * targetWeight) * right ^ 2 :=
        mul_le_mul_of_nonneg_right weightComparison rightSqNonneg
      _ = constant * (targetWeight * right ^ 2) := by ring
  have youngGap :
      0 ≤ left ^ 2 / sourceWeight + sourceWeight * right ^ 2 -
        2 * (left * right) := by
    rw [show
      left ^ 2 / sourceWeight + sourceWeight * right ^ 2 -
          2 * (left * right) =
        (left - sourceWeight * right) ^ 2 / sourceWeight by
      field_simp [sourceWeightPos.ne']
      ring]
    exact div_nonneg (sq_nonneg _) sourceWeightPos.le
  dsimp only [sourceWeight, targetWeight, constant] at weightedRight youngGap ⊢
  nlinarith

/-- Scalar H⁻¹×H¹ convolution at one fixed output.  The second
weighted row is reindexed by the canonical output-reflection equivalence. -/
theorem summable_fixedOutput_mixedWeightedProduct
    (output : IntegerWavevector)
    (left right : IntegerWavevector → Real)
    (leftNonneg : ∀ wave, 0 ≤ left wave)
    (rightNonneg : ∀ wave, 0 ≤ right wave)
    (leftNegativeOne : Summable fun wave : IntegerWavevector =>
      left wave ^ 2 / mixedLatticeWeight wave)
    (rightGradient : Summable fun wave : IntegerWavevector =>
      mixedLatticeWeight wave * right wave ^ 2) :
    Summable fun first : IntegerWavevector =>
      left first * right (output - first) := by
  have translatedGradient : Summable fun first : IntegerWavevector =>
      mixedLatticeWeight (output - first) *
        right (output - first) ^ 2 := by
    have reindexed := (outputSubEquiv output).summable_iff.mpr rightGradient
    exact reindexed.congr fun first => by
      rw [Function.comp_apply, outputSubEquiv_apply]
  have majorantSummable : Summable fun first : IntegerWavevector =>
      (1 / 2 : Real) *
        (left first ^ 2 / mixedLatticeWeight first +
          fixedOutputWeightConstant output *
            (mixedLatticeWeight (output - first) *
              right (output - first) ^ 2)) := by
    exact (leftNegativeOne.add
      (translatedGradient.mul_left
        (fixedOutputWeightConstant output))).mul_left (1 / 2 : Real)
  exact majorantSummable.of_nonneg_of_le
    (fun first => mul_nonneg (leftNonneg first)
      (rightNonneg (output - first)))
    (fun first => scalar_weightedYoung output first
      (left first) (right (output - first))
      (leftNonneg first) (rightNonneg (output - first)))

theorem summable_fixedOutput_gradientNegativeOneProduct
    (output : IntegerWavevector)
    (left right : IntegerWavevector → Real)
    (leftNonneg : ∀ wave, 0 ≤ left wave)
    (rightNonneg : ∀ wave, 0 ≤ right wave)
    (leftGradient : Summable fun wave : IntegerWavevector =>
      mixedLatticeWeight wave * left wave ^ 2)
    (rightNegativeOne : Summable fun wave : IntegerWavevector =>
      right wave ^ 2 / mixedLatticeWeight wave) :
    Summable fun first : IntegerWavevector =>
      left first * right (output - first) := by
  have reversed := summable_fixedOutput_mixedWeightedProduct
    output right left rightNonneg leftNonneg rightNegativeOne leftGradient
  have reindexed := (outputSubEquiv output).summable_iff.mpr reversed
  exact reindexed.congr fun first => by
    rw [Function.comp_apply, outputSubEquiv_apply]
    have reflected : output - (output - first) = first := by abel
    rw [reflected]
    ring

/-! ## Raw pair rows represented by their actual weighted sequences -/

/-- A single raw Fourier row bundled only so the existing sharp pair bound
can be reused. -/
def rawSingleState
    (wave : IntegerWavevector)
    (row : ComplexCoordinateVector) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState {wave} fun _ => row

@[simp] theorem rawSingleState_at
    (wave : IntegerWavevector)
    (row : ComplexCoordinateVector) :
    rawSingleState wave row wave = row := by
  simp [rawSingleState, finiteComplexVorticityState_apply]

/-- Euclidean amplitude of one raw row, read through the same physical
coefficient definition used by the existing bilinear estimate. -/
def rawRowAmplitude
    (row : IntegerWavevector → ComplexCoordinateVector)
    (wave : IntegerWavevector) : Real :=
  vorticityRowAmplitude (rawSingleState wave (row wave)) wave

theorem rawRowAmplitude_nonneg
    (row : IntegerWavevector → ComplexCoordinateVector)
    (wave : IntegerWavevector) :
    0 ≤ rawRowAmplitude row wave :=
  vorticityRowAmplitude_nonneg _ _

/-- One raw mixed pair.  Only the two displayed rows are installed in the
temporary bundled states; the value is therefore the literal pair formula. -/
def rawMixedBilinearPairContribution
    (left right : IntegerWavevector → ComplexCoordinateVector)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  finiteStateVorticityBilinearPairContribution
    (rawSingleState pair.1 (left pair.1))
    (rawSingleState pair.2 (right pair.2)) pair

theorem rawMixedBilinearPairContribution_norm_le
    (left right : IntegerWavevector → ComplexCoordinateVector)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (leftTransverse :
      complexWavevector first ⬝ᵥ left first = 0) :
    ‖rawMixedBilinearPairContribution left right (first, second)‖ ≤
      2 * Real.sqrt (integerWaveNormSq output) *
        rawRowAmplitude left first * rawRowAmplitude right second := by
  have bundledTransverse :
      complexWavevector first ⬝ᵥ
          rawSingleState first (left first) first = 0 := by
    simpa only [rawSingleState_at] using leftTransverse
  simpa only [rawMixedBilinearPairContribution, rawRowAmplitude] using
    finiteStateVorticityBilinearPairContribution_norm_le
      (rawSingleState first (left first))
      (rawSingleState second (right second))
      output first second incidence bundledTransverse

/-- H⁻¹ in the advecting slot, H¹ in the transported slot. -/
theorem summable_norm_rawMixedPair_negativeOne_gradient
    (output : IntegerWavevector)
    (left right : IntegerWavevector → ComplexCoordinateVector)
    (leftTransverse : ∀ wave,
      complexWavevector wave ⬝ᵥ left wave = 0)
    (leftNegativeOne : Summable fun wave : IntegerWavevector =>
      rawRowAmplitude left wave ^ 2 / mixedLatticeWeight wave)
    (rightGradient : Summable fun wave : IntegerWavevector =>
      mixedLatticeWeight wave * rawRowAmplitude right wave ^ 2) :
    Summable fun first : IntegerWavevector =>
      ‖rawMixedBilinearPairContribution
        left right (first, output - first)‖ := by
  have productSummable := summable_fixedOutput_mixedWeightedProduct
    output (rawRowAmplitude left) (rawRowAmplitude right)
    (rawRowAmplitude_nonneg left) (rawRowAmplitude_nonneg right)
    leftNegativeOne rightGradient
  let angular := 2 * Real.sqrt (integerWaveNormSq output)
  have majorantSummable : Summable fun first : IntegerWavevector =>
      angular * (rawRowAmplitude left first *
        rawRowAmplitude right (output - first)) :=
    productSummable.mul_left angular
  exact majorantSummable.of_nonneg_of_le
    (fun first => norm_nonneg _)
    (fun first => by
      have incidence : first + (output - first) = output := by abel
      simpa only [angular, mul_assoc] using
        rawMixedBilinearPairContribution_norm_le
          left right output first (output - first) incidence
            (leftTransverse first))

/-- H¹ in the advecting slot, H⁻¹ in the transported slot. -/
theorem summable_norm_rawMixedPair_gradient_negativeOne
    (output : IntegerWavevector)
    (left right : IntegerWavevector → ComplexCoordinateVector)
    (leftTransverse : ∀ wave,
      complexWavevector wave ⬝ᵥ left wave = 0)
    (leftGradient : Summable fun wave : IntegerWavevector =>
      mixedLatticeWeight wave * rawRowAmplitude left wave ^ 2)
    (rightNegativeOne : Summable fun wave : IntegerWavevector =>
      rawRowAmplitude right wave ^ 2 / mixedLatticeWeight wave) :
    Summable fun first : IntegerWavevector =>
      ‖rawMixedBilinearPairContribution
        left right (first, output - first)‖ := by
  have productSummable := summable_fixedOutput_gradientNegativeOneProduct
    output (rawRowAmplitude left) (rawRowAmplitude right)
    (rawRowAmplitude_nonneg left) (rawRowAmplitude_nonneg right)
    leftGradient rightNegativeOne
  let angular := 2 * Real.sqrt (integerWaveNormSq output)
  have majorantSummable : Summable fun first : IntegerWavevector =>
      angular * (rawRowAmplitude left first *
        rawRowAmplitude right (output - first)) :=
    productSummable.mul_left angular
  exact majorantSummable.of_nonneg_of_le
    (fun first => norm_nonneg _)
    (fun first => by
      have incidence : first + (output - first) = output := by abel
      simpa only [angular, mul_assoc] using
        rawMixedBilinearPairContribution_norm_le
          left right output first (output - first) incidence
            (leftTransverse first))

/-- Both mixed slots close under the same fixed-output source data. -/
theorem summable_both_rawMixedPair_slots
    (output : IntegerWavevector)
    (negative gradient : IntegerWavevector → ComplexCoordinateVector)
    (negativeTransverse : ∀ wave,
      complexWavevector wave ⬝ᵥ negative wave = 0)
    (gradientTransverse : ∀ wave,
      complexWavevector wave ⬝ᵥ gradient wave = 0)
    (negativeOne : Summable fun wave : IntegerWavevector =>
      rawRowAmplitude negative wave ^ 2 / mixedLatticeWeight wave)
    (gradientOne : Summable fun wave : IntegerWavevector =>
      mixedLatticeWeight wave * rawRowAmplitude gradient wave ^ 2) :
    (Summable fun first : IntegerWavevector =>
      rawMixedBilinearPairContribution
        negative gradient (first, output - first)) ∧
    (Summable fun first : IntegerWavevector =>
      rawMixedBilinearPairContribution
        gradient negative (first, output - first)) := by
  exact ⟨
    (summable_norm_rawMixedPair_negativeOne_gradient
      output negative gradient negativeTransverse negativeOne gradientOne).of_norm,
    (summable_norm_rawMixedPair_gradient_negativeOne
      output gradient negative gradientTransverse gradientOne negativeOne).of_norm⟩

/-! ## The finite normalized-work coface jet -/

open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

/-- Unit real coordinate atom at one Fourier row. -/
def finiteRealFourierCoordinateAtom
    (wave : IntegerWavevector)
    (coordinate : Coordinate) : ComplexVorticityHilbertState :=
  lp.single 2 wave (Pi.single coordinate 1)

/-- Unit imaginary coordinate atom at one Fourier row. -/
def finiteImaginaryFourierCoordinateAtom
    (wave : IntegerWavevector)
    (coordinate : Coordinate) : ComplexVorticityHilbertState :=
  lp.single 2 wave (Pi.single coordinate Complex.I)

/-- Canonical finite-coordinate representation of the real Frechet
functional.  The two real coefficients at every complex coordinate are
read by applying the derivative to its real and imaginary atoms. -/
def finiteNormalizedWorkJetTestCoefficient
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  fun coordinate =>
    ((fderiv Real (finiteNormalizedGeneratorWork modes viscosity) state)
        (finiteRealFourierCoordinateAtom wave coordinate) : Complex) +
      ((fderiv Real (finiteNormalizedGeneratorWork modes viscosity) state)
        (finiteImaginaryFourierCoordinateAtom wave coordinate) : Complex) *
        Complex.I

/-- The actual input-coface nonlinear correction retained on a full finite
cube.  It is the finite projection of `N(state) - N(projected state)`. -/
def finiteNormalizedWorkCofaceDirection
    (radius : Nat)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  let modes := integerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  finiteComplexVorticityState modes fun wave =>
    wholeStateVorticityNonlinearCoefficientAt state wave -
      wholeStateVorticityNonlinearCoefficientAt projected wave

/-- The normalized-work jet applied to the same finite input-coface
correction. -/
def finiteNormalizedWorkCofaceJet
    (radius : Nat)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) : Real :=
  let modes := integerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  (fderiv Real (finiteNormalizedGeneratorWork modes viscosity) projected)
    (finiteNormalizedWorkCofaceDirection radius state)

private theorem finiteComplexVorticityState_eq_sum_coordinateAtoms
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    finiteComplexVorticityState modes coefficient =
      ∑ wave ∈ modes, ∑ coordinate : Coordinate,
        ((coefficient wave coordinate).re •
            finiteRealFourierCoordinateAtom wave coordinate +
          (coefficient wave coordinate).im •
            finiteImaginaryFourierCoordinateAtom wave coordinate) := by
  apply lp.ext
  funext output
  funext coordinate
  rw [finiteComplexVorticityState_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_add,
    lp.coeFn_smul, Pi.add_apply, Pi.smul_apply]
  unfold finiteRealFourierCoordinateAtom
    finiteImaginaryFourierCoordinateAtom
  by_cases outputMem : output ∈ modes
  · rw [if_pos outputMem, Finset.sum_eq_single output]
    · rw [Finset.sum_eq_single coordinate]
      · simp [Pi.single_eq_same]
      · intro other _ otherNe
        simp [Pi.single_eq_of_ne otherNe.symm]
      · simp
    · intro other _ otherNe
      simp [Pi.single_eq_of_ne otherNe.symm]
    · intro outputNotMem
      exact False.elim (outputNotMem outputMem)
  · rw [if_neg outputMem]
    simp only [Pi.zero_apply]
    symm
    apply Finset.sum_eq_zero
    intro other otherMem
    have otherNe : output ≠ other := by
      intro outputEq
      exact outputMem (outputEq ▸ otherMem)
    simp [Pi.single_eq_of_ne otherNe]

private theorem fderiv_finiteComplexVorticityState_eq_testPairing
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    (fderiv Real (finiteNormalizedGeneratorWork modes viscosity) state)
        (finiteComplexVorticityState modes coefficient) =
      ∑ wave ∈ modes,
        complexCoordinateRealInner
          (finiteNormalizedWorkJetTestCoefficient
            modes viscosity state wave)
          (coefficient wave) := by
  rw [finiteComplexVorticityState_eq_sum_coordinateAtoms]
  simp_rw [map_sum, map_add, map_smul]
  unfold finiteNormalizedWorkJetTestCoefficient complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro wave _
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, add_zero, sub_zero, mul_one, smul_eq_mul]
  ring

/-- The Frechet jet is literally the finite `H¹` test pairing against the
same coface correction; the test coefficient is its canonical real-coordinate
dual readout, not an external witness. -/
theorem finiteNormalizedWorkCofaceJet_eq_pairing
    (radius : Nat)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) :
    let modes := integerWaveFrequencyCube radius
    let projected := complexSharpSupportProjection modes state
    finiteNormalizedWorkCofaceJet radius viscosity state =
      ∑ wave ∈ modes,
        complexCoordinateRealInner
          (finiteNormalizedWorkJetTestCoefficient
            modes viscosity projected wave)
          (wholeStateVorticityNonlinearCoefficientAt state wave -
            wholeStateVorticityNonlinearCoefficientAt projected wave) := by
  dsimp only
  rw [finiteNormalizedWorkCofaceJet,
    finiteNormalizedWorkCofaceDirection]
  exact fderiv_finiteComplexVorticityState_eq_testPairing _ _ _ _

/-- The coface jet is controlled by the existing whole nonlinear `H⁻¹`
difference mass.  The finite `H¹` test energy is generated from the
normalized-work gradient on the identical projected state. -/
theorem finiteNormalizedWorkCofaceJet_sq_le_negativeOne
    (radius : Nat)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector ↦
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    let modes := integerWaveFrequencyCube radius
    let nonzeroModes := modes.erase 0
    let projected := complexSharpSupportProjection modes state
    finiteNormalizedWorkCofaceJet radius viscosity state ^ 2 ≤
      (∑ wave ∈ nonzeroModes,
          3 * integerWaveViscousMultiplier wave *
            complexCoordinateAmplitudeSq
              (finiteNormalizedWorkJetTestCoefficient
                modes viscosity projected wave)) *
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          projected state := by
  dsimp only
  let modes := integerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  let testCoefficient :=
    finiteNormalizedWorkJetTestCoefficient modes viscosity projected
  have projectedTransverse : WholeStateTransverse projected := by
    intro wave
    by_cases waveMem : wave ∈ modes
    · simpa [projected, complexSharpSupportProjection_apply, waveMem] using
        stateTransverse wave
    · simp [projected, complexSharpSupportProjection_apply, waveMem]
  have stateNonlinearZero :
      wholeStateVorticityNonlinearCoefficientAt state 0 = 0 :=
    wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
      state stateTransverse
  have projectedNonlinearZero :
      wholeStateVorticityNonlinearCoefficientAt projected 0 = 0 :=
    wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
      projected projectedTransverse
  have jetEq :
      finiteNormalizedWorkCofaceJet radius viscosity state =
        -(∑ wave ∈ modes.erase 0,
          complexCoordinateRealInner (testCoefficient wave)
            (wholeStateVorticityNonlinearCoefficientAt projected wave -
              wholeStateVorticityNonlinearCoefficientAt state wave)) := by
    rw [finiteNormalizedWorkCofaceJet_eq_pairing]
    have zeroTerm :
        complexCoordinateRealInner (testCoefficient 0)
          (wholeStateVorticityNonlinearCoefficientAt state 0 -
            wholeStateVorticityNonlinearCoefficientAt projected 0) = 0 := by
      rw [stateNonlinearZero, projectedNonlinearZero, sub_self,
        complexCoordinateRealInner_zero_right]
    have eraseEq :
        (∑ wave ∈ modes,
          complexCoordinateRealInner (testCoefficient wave)
            (wholeStateVorticityNonlinearCoefficientAt state wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave)) =
        ∑ wave ∈ modes.erase 0,
          complexCoordinateRealInner (testCoefficient wave)
            (wholeStateVorticityNonlinearCoefficientAt state wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave) := by
      by_cases zeroMem : (0 : IntegerWavevector) ∈ modes
      · have eraseAdd := Finset.sum_erase_add
          (s := modes)
          (f := fun wave ↦
            complexCoordinateRealInner (testCoefficient wave)
              (wholeStateVorticityNonlinearCoefficientAt state wave -
                wholeStateVorticityNonlinearCoefficientAt projected wave))
          zeroMem
        rw [zeroTerm, add_zero] at eraseAdd
        exact eraseAdd.symm
      · rw [Finset.erase_eq_of_notMem zeroMem]
    rw [eraseEq]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro wave _
    rw [complexCoordinateRealInner_sub_right]
    rw [complexCoordinateRealInner_sub_right]
    ring
  rw [jetEq, neg_sq]
  exact finiteNonlinearProjectionPairing_sq_le_testEnergy_mul_differenceMass
    state stateTransverse gradientSummable radius (modes.erase 0)
      (fun wave waveMem ↦ (Finset.mem_erase.mp waveMem).1) testCoefficient

/-- The existing Agmon projection estimate turns the exact negative-one
escrow into a source-computed inverse-radius bound.  The finite dual energy
is retained explicitly; no residual sign or future horizon is assumed. -/
theorem finiteNormalizedWorkCofaceJet_sq_le_agmon
    (radius : Nat)
    (radiusPos : 0 < radius)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector ↦
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    let modes := integerWaveFrequencyCube radius
    let nonzeroModes := modes.erase 0
    let projected := complexSharpSupportProjection modes state
    finiteNormalizedWorkCofaceJet radius viscosity state ^ 2 ≤
      (∑ wave ∈ nonzeroModes,
          3 * integerWaveViscousMultiplier wave *
            complexCoordinateAmplitudeSq
              (finiteNormalizedWorkJetTestCoefficient
                modes viscosity projected wave)) *
        (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          wholeVorticityEuclideanMass state *
          wholeStateVorticityGradientMass state) := by
  dsimp only
  let modes := integerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  let testEnergy :=
    ∑ wave ∈ modes.erase 0,
      3 * integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq
          (finiteNormalizedWorkJetTestCoefficient
            modes viscosity projected wave)
  have testEnergyNonneg : 0 ≤ testEnergy := by
    dsimp only [testEnergy]
    exact Finset.sum_nonneg fun wave _ =>
      mul_nonneg
        (mul_nonneg (by norm_num) (by
          unfold integerWaveViscousMultiplier
          exact mul_nonneg (sq_nonneg _)
            (integerWaveNormSq_nonneg wave)))
        (complexCoordinateAmplitudeSq_nonneg _)
  have jetBound := finiteNormalizedWorkCofaceJet_sq_le_negativeOne
    radius viscosity state stateTransverse gradientSummable
  have differenceBound :=
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_le_agmon
      state stateTransverse gradientSummable radius radiusPos
  exact jetBound.trans
    (mul_le_mul_of_nonneg_left differenceBound testEnergyNonneg)

end

end ThreeDimensionalVorticityCoefficientMixedNegativeOneGradientFixedOutput
end NavierStokes
end SaturationMonoid
