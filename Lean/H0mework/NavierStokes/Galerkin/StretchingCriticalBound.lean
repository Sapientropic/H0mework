import H0mework.NavierStokes.Galerkin.EnstrophyBalance

/-!
# Cutoff-independent critical bound for finite Galerkin stretching

This module estimates the complete finite vorticity stretching work on its
actual interaction inventory.  Transversality moves the derivative frequency
from the velocity slot to the output vorticity slot.  The remaining
convolution is then grouped by the velocity frequency and estimated by a
translation-invariant finite Cauchy--Schwarz inequality.  Consequently no
mode-cardinality or maximal-frequency factor appears.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance

noncomputable section

private def vorticityAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt (complexCoordinateAmplitudeSq (state wave))

private def velocityAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt
    (complexCoordinateAmplitudeSq
      (finiteStateVelocityCoefficient state wave))

private def vorticityGradientAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt
    ((2 * Real.pi) ^ 2 * integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (state wave))

private theorem vorticityAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ vorticityAmplitude state wave :=
  Real.sqrt_nonneg _

private theorem velocityAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ velocityAmplitude state wave :=
  Real.sqrt_nonneg _

private theorem vorticityGradientAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ vorticityGradientAmplitude state wave :=
  Real.sqrt_nonneg _

private theorem vorticityAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    vorticityAmplitude state wave ^ 2 =
      complexCoordinateAmplitudeSq (state wave) := by
  rw [vorticityAmplitude, Real.sq_sqrt]
  exact complexCoordinateAmplitudeSq_nonneg _

private theorem velocityAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    velocityAmplitude state wave ^ 2 =
      complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave) := by
  rw [velocityAmplitude, Real.sq_sqrt]
  exact complexCoordinateAmplitudeSq_nonneg _

private theorem vorticityGradientAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    vorticityGradientAmplitude state wave ^ 2 =
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (state wave) := by
  rw [vorticityGradientAmplitude, Real.sq_sqrt]
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
    (complexCoordinateAmplitudeSq_nonneg _)

/-- Cauchy--Schwarz on the actual three-coordinate real Hermitian pairing.
This carrier-level inequality is reused by whole-flow occurrence ledgers. -/
theorem complexCoordinateRealInner_sq_le
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right ^ 2 ≤
      complexCoordinateAmplitudeSq left *
        complexCoordinateAmplitudeSq right := by
  have coordinateBound :
      ∀ coordinate : Coordinate,
        ((left coordinate).re * (right coordinate).re +
            (left coordinate).im * (right coordinate).im) ^ 2 ≤
          Complex.normSq (left coordinate) *
            Complex.normSq (right coordinate) := by
    intro coordinate
    rw [Complex.normSq_apply, Complex.normSq_apply]
    nlinarith
      [sq_nonneg
        ((left coordinate).re * (right coordinate).im -
          (left coordinate).im * (right coordinate).re)]
  have cauchy :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset Coordinate)
      (r := fun coordinate =>
        (left coordinate).re * (right coordinate).re +
          (left coordinate).im * (right coordinate).im)
      (f := fun coordinate => Complex.normSq (left coordinate))
      (g := fun coordinate => Complex.normSq (right coordinate))
      (fun coordinate _ => Complex.normSq_nonneg _)
      (fun coordinate _ => Complex.normSq_nonneg _)
      (fun coordinate _ => coordinateBound coordinate)
  simpa [complexCoordinateRealInner, complexCoordinateAmplitudeSq] using cauchy

private theorem complexWavevector_dot_normSq_le
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    Complex.normSq (complexWavevector wave ⬝ᵥ vector) ≤
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq vector := by
  have identity :=
    complexWavevector_cross_normSq wave vector
  have crossNonneg :=
    complexCoordinateVectorNormSq_nonneg
      (complexWavevector wave ⨯₃ vector)
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  linarith

private theorem complexWavevector_add_local
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

private theorem second_dot_eq_output_dot_of_transverse
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ state first = 0) :
    complexWavevector second ⬝ᵥ state first =
      complexWavevector output ⬝ᵥ state first := by
  rw [← incidence, complexWavevector_add_local, add_dotProduct, transverse]
  simp

private theorem stretchingPairContribution_amplitudeSq_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ state first = 0) :
    complexCoordinateAmplitudeSq
        (finiteStateVorticityStretchingPairContribution
          state (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq (state first) *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le output (state first)
  rw [← second_dot_eq_output_dot_of_transverse
    state output first second incidence transverse] at dotBound
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVorticityStretchingPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have angularNonneg : 0 ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg _
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound angularNonneg)
      (complexCoordinateVectorNormSq_nonneg
        (finiteStateVelocityCoefficient state second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem stretchingOccurrenceWork_abs_le
    (state : ComplexVorticityHilbertState)
    (occurrence : FiniteVorticityInteractionOccurrence)
    (incidence :
      finiteVorticityInteractionFirst occurrence +
          finiteVorticityInteractionSecond occurrence =
        finiteVorticityInteractionOutput occurrence)
    (transverse :
      complexWavevector
            (finiteVorticityInteractionFirst occurrence) ⬝ᵥ
          state (finiteVorticityInteractionFirst occurrence) = 0) :
    |finiteStateVorticityStretchingOccurrenceWork state occurrence| ≤
      velocityAmplitude state
          (finiteVorticityInteractionSecond occurrence) *
        vorticityAmplitude state
          (finiteVorticityInteractionFirst occurrence) *
        vorticityGradientAmplitude state
          (finiteVorticityInteractionOutput occurrence) := by
  let output := finiteVorticityInteractionOutput occurrence
  let first := finiteVorticityInteractionFirst occurrence
  let second := finiteVorticityInteractionSecond occurrence
  have innerBound :=
    complexCoordinateRealInner_sq_le
      (state output)
      (finiteStateVorticityStretchingPairContribution
        state (first, second))
  have pairBound :=
    stretchingPairContribution_amplitudeSq_le
      state output first second incidence transverse
  have outputNonneg :=
    complexCoordinateAmplitudeSq_nonneg (state output)
  have combined :
      finiteStateVorticityStretchingOccurrenceWork state occurrence ^ 2 ≤
        (velocityAmplitude state second *
          vorticityAmplitude state first *
          vorticityGradientAmplitude state output) ^ 2 := by
    calc
      finiteStateVorticityStretchingOccurrenceWork state occurrence ^ 2 ≤
          complexCoordinateAmplitudeSq (state output) *
            complexCoordinateAmplitudeSq
              (finiteStateVorticityStretchingPairContribution
                state (first, second)) := by
        simpa [finiteStateVorticityStretchingOccurrenceWork,
          output, first, second] using innerBound
      _ ≤
          complexCoordinateAmplitudeSq (state output) *
            ((2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq (state first) *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient state second)) :=
        mul_le_mul_of_nonneg_left pairBound outputNonneg
      _ =
          (velocityAmplitude state second *
            vorticityAmplitude state first *
            vorticityGradientAmplitude state output) ^ 2 := by
        simp only [mul_pow, velocityAmplitude_sq,
          vorticityAmplitude_sq, vorticityGradientAmplitude_sq]
        ring
  exact
    (sq_le_sq₀
      (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg
          (velocityAmplitude_nonneg state second)
          (vorticityAmplitude_nonneg state first))
        (vorticityGradientAmplitude_nonneg state output))).mp
      (by simpa [sq_abs] using combined)

/-! ## Interaction slices and translation-free Cauchy--Schwarz -/

private def finiteVorticityInteractionSlice
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector) :
    Finset (IntegerWavevector × IntegerWavevector) :=
  (modes ×ˢ modes).filter fun outputFirst =>
    outputFirst.2 + second = outputFirst.1

private theorem sum_interactionInventory_eq_sum_slices
    (modes : Finset IntegerWavevector)
    (f : FiniteVorticityInteractionOccurrence → ℝ) :
    (∑ occurrence ∈ finiteVorticityInteractionInventory modes,
        f occurrence) =
      ∑ second ∈ modes,
        ∑ outputFirst ∈
            finiteVorticityInteractionSlice modes second,
          f (outputFirst, second) := by
  unfold finiteVorticityInteractionInventory
    finiteVorticityInteractionSlice
  simp only [Finset.sum_filter, Finset.sum_product]
  calc
    (∑ output ∈ modes,
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              f ((output, first), second)
            else 0) =
      ∑ output ∈ modes,
        ∑ second ∈ modes,
          ∑ first ∈ modes,
            if first + second = output then
              f ((output, first), second)
            else 0 := by
      apply Finset.sum_congr rfl
      intro output outputMem
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem interactionSlice_first_injective
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector) :
    Set.InjOn Prod.snd
      (finiteVorticityInteractionSlice modes second : Set
        (IntegerWavevector × IntegerWavevector)) := by
  intro left leftMem right rightMem sameFirst
  have leftIncidence :=
    (Finset.mem_filter.mp leftMem).2
  have rightIncidence :=
    (Finset.mem_filter.mp rightMem).2
  apply Prod.ext
  · calc
      left.1 = left.2 + second := leftIncidence.symm
      _ = right.2 + second := by rw [sameFirst]
      _ = right.1 := rightIncidence
  · exact sameFirst

private theorem interactionSlice_output_injective
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector) :
    Set.InjOn Prod.fst
      (finiteVorticityInteractionSlice modes second : Set
        (IntegerWavevector × IntegerWavevector)) := by
  intro left leftMem right rightMem sameOutput
  have leftIncidence :=
    (Finset.mem_filter.mp leftMem).2
  have rightIncidence :=
    (Finset.mem_filter.mp rightMem).2
  apply Prod.ext
  · exact sameOutput
  · exact add_right_cancel
      (leftIncidence.trans (sameOutput.trans rightIncidence.symm))

private theorem interactionSlice_first_sum_le
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ outputFirst ∈ finiteVorticityInteractionSlice modes second,
        complexCoordinateAmplitudeSq (state outputFirst.2)) ≤
      ∑ first ∈ modes,
        complexCoordinateAmplitudeSq (state first) := by
  let firstImage :=
    (finiteVorticityInteractionSlice modes second).image Prod.snd
  have imageSubset : firstImage ⊆ modes := by
    intro first firstMem
    rcases Finset.mem_image.mp firstMem with
      ⟨outputFirst, sliceMem, rfl⟩
    exact (Finset.mem_product.mp
      (Finset.mem_filter.mp sliceMem).1).2
  calc
    (∑ outputFirst ∈ finiteVorticityInteractionSlice modes second,
        complexCoordinateAmplitudeSq (state outputFirst.2)) =
      ∑ first ∈ firstImage,
        complexCoordinateAmplitudeSq (state first) := by
          symm
          exact Finset.sum_image
            (interactionSlice_first_injective modes second)
    _ ≤
      ∑ first ∈ modes,
        complexCoordinateAmplitudeSq (state first) :=
      Finset.sum_le_sum_of_subset_of_nonneg imageSubset
        (fun first firstMem firstNotMem =>
          complexCoordinateAmplitudeSq_nonneg _)

private theorem interactionSlice_outputGradient_sum_le
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ outputFirst ∈ finiteVorticityInteractionSlice modes second,
        (2 * Real.pi) ^ 2 * integerWaveNormSq outputFirst.1 *
          complexCoordinateAmplitudeSq (state outputFirst.1)) ≤
      ∑ output ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq (state output) := by
  let outputImage :=
    (finiteVorticityInteractionSlice modes second).image Prod.fst
  have imageSubset : outputImage ⊆ modes := by
    intro output outputMem
    rcases Finset.mem_image.mp outputMem with
      ⟨outputFirst, sliceMem, rfl⟩
    exact (Finset.mem_product.mp
      (Finset.mem_filter.mp sliceMem).1).1
  calc
    (∑ outputFirst ∈ finiteVorticityInteractionSlice modes second,
        (2 * Real.pi) ^ 2 * integerWaveNormSq outputFirst.1 *
          complexCoordinateAmplitudeSq (state outputFirst.1)) =
      ∑ output ∈ outputImage,
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq (state output) := by
          symm
          exact Finset.sum_image
            (interactionSlice_output_injective modes second)
    _ ≤
      ∑ output ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq (state output) :=
      Finset.sum_le_sum_of_subset_of_nonneg imageSubset
        (fun output outputMem outputNotMem =>
          mul_nonneg
            (mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg output))
            (complexCoordinateAmplitudeSq_nonneg _))

private theorem interactionSlice_cauchy
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ outputFirst ∈ finiteVorticityInteractionSlice modes second,
        vorticityAmplitude state outputFirst.2 *
          vorticityGradientAmplitude state outputFirst.1) ≤
      Real.sqrt
          (∑ first ∈ modes,
            complexCoordinateAmplitudeSq (state first)) *
        Real.sqrt
          (∑ output ∈ modes,
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq (state output)) := by
  have cauchy :=
    Real.sum_sqrt_mul_sqrt_le
      (finiteVorticityInteractionSlice modes second)
      (f := fun outputFirst =>
        complexCoordinateAmplitudeSq (state outputFirst.2))
      (g := fun outputFirst =>
        (2 * Real.pi) ^ 2 * integerWaveNormSq outputFirst.1 *
          complexCoordinateAmplitudeSq (state outputFirst.1))
      (fun outputFirst =>
        complexCoordinateAmplitudeSq_nonneg _)
      (fun outputFirst =>
        mul_nonneg
          (mul_nonneg (sq_nonneg _)
            (integerWaveNormSq_nonneg outputFirst.1))
          (complexCoordinateAmplitudeSq_nonneg _))
  have firstBound :=
    interactionSlice_first_sum_le modes second state
  have outputBound :=
    interactionSlice_outputGradient_sum_le modes second state
  calc
    (∑ outputFirst ∈ finiteVorticityInteractionSlice modes second,
        vorticityAmplitude state outputFirst.2 *
          vorticityGradientAmplitude state outputFirst.1) ≤
      Real.sqrt
          (∑ outputFirst ∈
            finiteVorticityInteractionSlice modes second,
            complexCoordinateAmplitudeSq (state outputFirst.2)) *
        Real.sqrt
          (∑ outputFirst ∈
            finiteVorticityInteractionSlice modes second,
            (2 * Real.pi) ^ 2 *
              integerWaveNormSq outputFirst.1 *
              complexCoordinateAmplitudeSq
                (state outputFirst.1)) := by
      simpa [vorticityAmplitude,
        vorticityGradientAmplitude] using cauchy
    _ ≤
      Real.sqrt
          (∑ first ∈ modes,
            complexCoordinateAmplitudeSq (state first)) *
        Real.sqrt
          (∑ output ∈ modes,
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq (state output)) := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt firstBound)
        (Real.sqrt_le_sqrt outputBound)
        (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)

/-!
The complete stretching work satisfies the endpoint critical estimate with
constant one.  The theorem is uniform in the finite inventory: no mode count,
maximal shell, selected path, or target lifespan appears at its mouth.
-/
theorem finiteStateVorticityStretchingWork_abs_le_critical
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    |finiteStateVorticityStretchingWork modes state| ≤
      finiteStateVelocityMajorant modes state *
        Real.sqrt
          (finiteStateVorticityCoefficientEnstrophy modes state) *
        Real.sqrt
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) := by
  let coefficientEnstrophy :=
    ∑ wave ∈ modes,
      complexCoordinateAmplitudeSq (state wave)
  let gradientEnstrophy :=
    ∑ wave ∈ modes,
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (state wave)
  have occurrenceSum :
      (∑ occurrence ∈ finiteVorticityInteractionInventory modes,
          |finiteStateVorticityStretchingOccurrenceWork
            state occurrence|) =
        ∑ second ∈ modes,
          ∑ outputFirst ∈
              finiteVorticityInteractionSlice modes second,
            |finiteStateVorticityStretchingOccurrenceWork
              state (outputFirst, second)| :=
    sum_interactionInventory_eq_sum_slices modes _
  have pointwiseSum :
      (∑ second ∈ modes,
          ∑ outputFirst ∈
              finiteVorticityInteractionSlice modes second,
            |finiteStateVorticityStretchingOccurrenceWork
              state (outputFirst, second)|) ≤
        ∑ second ∈ modes,
          velocityAmplitude state second *
            (∑ outputFirst ∈
                finiteVorticityInteractionSlice modes second,
              vorticityAmplitude state outputFirst.2 *
                vorticityGradientAmplitude state outputFirst.1) := by
    apply Finset.sum_le_sum
    intro second secondMem
    calc
      (∑ outputFirst ∈
          finiteVorticityInteractionSlice modes second,
          |finiteStateVorticityStretchingOccurrenceWork
            state (outputFirst, second)|) ≤
        ∑ outputFirst ∈
            finiteVorticityInteractionSlice modes second,
          velocityAmplitude state second *
            (vorticityAmplitude state outputFirst.2 *
              vorticityGradientAmplitude state outputFirst.1) := by
        apply Finset.sum_le_sum
        intro outputFirst outputFirstMem
        have productMem :=
          (Finset.mem_filter.mp outputFirstMem).1
        have firstMem :=
          (Finset.mem_product.mp productMem).2
        have incidence :=
          (Finset.mem_filter.mp outputFirstMem).2
        simpa only [
          finiteVorticityInteractionOutput,
          finiteVorticityInteractionFirst,
          finiteVorticityInteractionSecond,
          mul_assoc] using
          stretchingOccurrenceWork_abs_le
            state (outputFirst, second) incidence
              (transverse outputFirst.2 firstMem)
      _ =
        velocityAmplitude state second *
          (∑ outputFirst ∈
              finiteVorticityInteractionSlice modes second,
            vorticityAmplitude state outputFirst.2 *
              vorticityGradientAmplitude state outputFirst.1) := by
        rw [Finset.mul_sum]
  have slicedCauchy :
      (∑ second ∈ modes,
          velocityAmplitude state second *
            (∑ outputFirst ∈
                finiteVorticityInteractionSlice modes second,
              vorticityAmplitude state outputFirst.2 *
                vorticityGradientAmplitude state outputFirst.1)) ≤
        ∑ second ∈ modes,
          velocityAmplitude state second *
            (Real.sqrt coefficientEnstrophy *
              Real.sqrt gradientEnstrophy) := by
    apply Finset.sum_le_sum
    intro second secondMem
    exact mul_le_mul_of_nonneg_left
      (by simpa [coefficientEnstrophy, gradientEnstrophy] using
        interactionSlice_cauchy modes second state)
      (velocityAmplitude_nonneg state second)
  calc
    |finiteStateVorticityStretchingWork modes state| ≤
        ∑ occurrence ∈ finiteVorticityInteractionInventory modes,
          |finiteStateVorticityStretchingOccurrenceWork
            state occurrence| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ =
        ∑ second ∈ modes,
          ∑ outputFirst ∈
              finiteVorticityInteractionSlice modes second,
            |finiteStateVorticityStretchingOccurrenceWork
              state (outputFirst, second)| :=
      occurrenceSum
    _ ≤
        ∑ second ∈ modes,
          velocityAmplitude state second *
            (∑ outputFirst ∈
                finiteVorticityInteractionSlice modes second,
              vorticityAmplitude state outputFirst.2 *
                vorticityGradientAmplitude state outputFirst.1) :=
      pointwiseSum
    _ ≤
        ∑ second ∈ modes,
          velocityAmplitude state second *
            (Real.sqrt coefficientEnstrophy *
              Real.sqrt gradientEnstrophy) :=
      slicedCauchy
    _ =
        finiteStateVelocityMajorant modes state *
          Real.sqrt
            (finiteStateVorticityCoefficientEnstrophy modes state) *
          Real.sqrt
            ((2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes state) := by
      rw [← Finset.sum_mul]
      unfold coefficientEnstrophy gradientEnstrophy
      unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
        velocityAmplitude finiteStateVorticityCoefficientEnstrophy
        finiteStateVorticityEnstrophyMass
      rw [Finset.mul_sum]
      ring_nf

/-!
Young absorption with the exact viscous gradient normalization.  The first
right-hand term is one half of the viscous term in the enstrophy ledger; the
second is the endpoint-Serrin coefficient multiplying ordinary enstrophy.
-/
theorem finiteStateVorticityStretchingWork_abs_le_young
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (ν : ℝ)
    (ν_pos : 0 < ν)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    |finiteStateVorticityStretchingWork modes state| ≤
      (ν / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        (ν⁻¹ / 2) *
          finiteStateVelocityMajorant modes state ^ 2 *
          finiteStateVorticityCoefficientEnstrophy modes state := by
  let gradientEnstrophy :=
    (2 * Real.pi) ^ 2 *
      finiteStateVorticityEnstrophyMass modes state
  let coefficientEnstrophy :=
    finiteStateVorticityCoefficientEnstrophy modes state
  let majorant :=
    finiteStateVelocityMajorant modes state
  have gradientNonneg : 0 ≤ gradientEnstrophy := by
    exact mul_nonneg (sq_nonneg _)
      (finiteStateVorticityEnstrophyMass_nonneg modes state)
  have coefficientNonneg : 0 ≤ coefficientEnstrophy := by
    unfold coefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have criticalBound :
      |finiteStateVorticityStretchingWork modes state| ≤
        majorant * Real.sqrt coefficientEnstrophy *
          Real.sqrt gradientEnstrophy := by
    simpa [majorant, coefficientEnstrophy, gradientEnstrophy] using
      finiteStateVorticityStretchingWork_abs_le_critical
        modes state transverse
  have young :=
    two_mul_le_add_mul_sq
      (a := Real.sqrt gradientEnstrophy)
      (b := majorant * Real.sqrt coefficientEnstrophy)
      ν_pos
  have doubled :
      2 * |finiteStateVorticityStretchingWork modes state| ≤
        ν * gradientEnstrophy +
          ν⁻¹ * majorant ^ 2 * coefficientEnstrophy := by
    calc
      2 * |finiteStateVorticityStretchingWork modes state| ≤
          2 * (majorant * Real.sqrt coefficientEnstrophy *
            Real.sqrt gradientEnstrophy) :=
        mul_le_mul_of_nonneg_left criticalBound (by norm_num)
      _ =
          2 * Real.sqrt gradientEnstrophy *
            (majorant * Real.sqrt coefficientEnstrophy) := by
        ring
      _ ≤
          ν * Real.sqrt gradientEnstrophy ^ 2 +
            ν⁻¹ *
              (majorant * Real.sqrt coefficientEnstrophy) ^ 2 :=
        young
      _ =
          ν * gradientEnstrophy +
            ν⁻¹ * majorant ^ 2 * coefficientEnstrophy := by
        rw [Real.sq_sqrt gradientNonneg,
          mul_pow, Real.sq_sqrt coefficientNonneg]
        ring
  dsimp [gradientEnstrophy, coefficientEnstrophy, majorant] at doubled
  nlinarith

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
end NavierStokes
end SaturationMonoid
