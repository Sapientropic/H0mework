import H0mework.NavierStokes.Fourier.WholeVelocityFixedOutputNonlinearRow
import H0mework.NavierStokes.Energy.StrongContinuationDifferenceKineticEnergy
import H0mework.NavierStokes.Energy.FiniteKineticDifferenceCancellation

/-!
# Whole velocity pair diagonal in the negative-one carrier

Before the fixed-output pair quotient, one ordered velocity-convection
occurrence has an exact negative-one square cost.  Transversality moves its
derivative to the generated output, where the inverse Laplacian weight
cancels it.  Summing over every ordered input pair therefore costs at most
the square of the actual whole velocity mass.

This is the paid diagonal part of the Navier--Stokes pair-interference gate.
It does not bound the square of the aggregated fixed-output row: that
difference is precisely the cross-pair interference still requiring native
gluing settlement.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy

noncomputable section

/-! ## The complete physical velocity on the common whole carrier -/

/-- Install the Biot--Savart velocity of a whole vorticity state on the same
all-wave Hilbert carrier used by the pair convolution.  The zero wave is
definitionally silent; no cutoff or support certificate is used. -/
def wholeBiotSavartVelocityState
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  ⟨finiteStateVelocityCoefficient state, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Summable.of_nonneg_of_le
        (fun wave =>
          sq_nonneg ‖finiteStateVelocityCoefficient state wave‖)
        (fun wave => by
          calc
            ‖finiteStateVelocityCoefficient state wave‖ ^ 2 ≤
                velocityRowAmplitude state wave ^ 2 := by
              rw [velocityRowAmplitude_sq]
              exact complexCoordinateVector_norm_sq_le_amplitudeSq _
            _ ≤ vorticityRowAmplitude state wave ^ 2 := by
              have rowLe :=
                velocityRowAmplitude_le_vorticityRowAmplitude state wave
              have factorLe : (1 / (2 * Real.pi) : ℝ) ≤ 1 := by
                apply
                  (div_le_iff₀
                    (by positivity : (0 : ℝ) < 2 * Real.pi)).2
                nlinarith [Real.pi_gt_three]
              have scaledLe :
                  (1 / (2 * Real.pi)) *
                        vorticityRowAmplitude state wave ≤
                    vorticityRowAmplitude state wave :=
                mul_le_of_le_one_left
                  (vorticityRowAmplitude_nonneg state wave) factorLe
              exact
                (sq_le_sq₀
                  (velocityRowAmplitude_nonneg state wave)
                  (vorticityRowAmplitude_nonneg state wave)).2
                    (rowLe.trans scaledLe))
        (summable_vorticityRowAmplitude_sq state)⟩

@[simp] theorem wholeBiotSavartVelocityState_apply
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    wholeBiotSavartVelocityState state wave =
      finiteStateVelocityCoefficient state wave :=
  rfl

/-- The installed physical velocity is transverse without a premise: this is
the Biot--Savart identity on every actual wave. -/
theorem wholeBiotSavartVelocityState_transverse
    (state : ComplexVorticityHilbertState) :
    WholeStateTransverse (wholeBiotSavartVelocityState state) := by
  intro wave
  exact complexWavevector_dot_biotSavartVelocityCoefficient wave (state wave)

/-- Forming one ordered velocity-convection occurrence commutes literally
with installation of the Biot--Savart velocity on the whole carrier. -/
theorem
    wholeStateVelocityBilinearPairContribution_wholeBiotSavartVelocityState
    (state : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    wholeStateVelocityBilinearPairContribution
        (wholeBiotSavartVelocityState state)
        (wholeBiotSavartVelocityState state) pair =
      finiteStateVelocityBilinearPairContribution state state pair := by
  rfl

/-- For a transverse vorticity state, the Euclidean mass of the installed
whole velocity is exactly the established physical kinetic mass.  The
all-wave carrier therefore introduces neither a new norm nor an unpaid zero
mode. -/
theorem wholeVorticityEuclideanMass_wholeBiotSavartVelocityState
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    wholeVorticityEuclideanMass (wholeBiotSavartVelocityState state) =
      puncturedWholeVorticityKineticMass state := by
  let mass : IntegerWavevector → ℝ := fun wave =>
    complexCoordinateAmplitudeSq
      (wholeBiotSavartVelocityState state wave)
  have massSummable : Summable mass := by
    exact
      (summable_vorticityRowAmplitude_sq
        (wholeBiotSavartVelocityState state)).congr
        (fun wave =>
          vorticityRowAmplitude_sq
            (wholeBiotSavartVelocityState state) wave)
  have complementZero :
      (∑' wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector),
        mass wave.1) =
        0 := by
    rw [show
        (fun wave :
            ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
              Set IntegerWavevector) =>
          mass wave.1) =
          0 by
        funext wave
        simp only [Pi.zero_apply]
        have waveZero : wave.1 = 0 := by simpa using wave.2
        rw [waveZero]
        simp [mass, wholeBiotSavartVelocityState,
          finiteStateVelocityCoefficient,
          biotSavartVelocityCoefficient_zero,
          complexCoordinateAmplitudeSq]]
    exact tsum_zero
  have split :=
    massSummable.tsum_subtype_add_tsum_subtype_compl
      { wave : IntegerWavevector | wave ≠ 0 }
  unfold wholeVorticityEuclideanMass
    puncturedWholeVorticityKineticMass
  rw [show
      (fun wave : IntegerWavevector =>
        vorticityRowAmplitude
            (wholeBiotSavartVelocityState state) wave ^ 2) =
        mass by
      funext wave
      exact
        vorticityRowAmplitude_sq
          (wholeBiotSavartVelocityState state) wave]
  rw [← split, complementZero, add_zero]
  apply tsum_congr
  intro wave
  unfold mass
  rw [wholeBiotSavartVelocityState_apply,
    finiteStateVelocityCoefficient,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    biotSavartVelocityCoefficient_normSq_of_transverse
      wave.1 (state wave.1) wave.2 (transverse wave.1),
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rfl

/-! ## Ordered-pair negative-one diagonal -/

/-- Exact ordered-pair diagonal density after installing the inverse output
Laplacian weight.  The zero output is assigned zero. -/
def wholeVelocityPairNegativeOneDiagonalDensity
    (velocity : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) : ℝ :=
  let output := pair.1 + pair.2
  if output = 0 then 0
  else
    ‖wholeStateVelocityBilinearPairContribution
        velocity velocity pair‖ ^ 2 /
      integerWaveViscousMultiplier output

theorem wholeVelocityPairNegativeOneDiagonalDensity_nonneg
    (velocity : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    0 ≤ wholeVelocityPairNegativeOneDiagonalDensity velocity pair := by
  unfold wholeVelocityPairNegativeOneDiagonalDensity
  dsimp only
  split_ifs
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _)
      (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg _))

/-- One ordered occurrence is paid by the product of its two input velocity
row masses.  No cutoff, output multiplicity, or ambient frequency appears. -/
theorem wholeVelocityPairNegativeOneDiagonalDensity_le
    (velocity : ComplexVorticityHilbertState)
    (velocityTransverse : WholeStateTransverse velocity)
    (pair : IntegerWavevector × IntegerWavevector) :
    wholeVelocityPairNegativeOneDiagonalDensity velocity pair ≤
      vorticityRowAmplitude velocity pair.1 ^ 2 *
        vorticityRowAmplitude velocity pair.2 ^ 2 := by
  let output := pair.1 + pair.2
  by_cases outputZero : output = 0
  · rw [wholeVelocityPairNegativeOneDiagonalDensity]
    rw [if_pos outputZero]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · have multiplierPos :
        0 < integerWaveViscousMultiplier output := by
      unfold integerWaveViscousMultiplier
      exact mul_pos
        (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
        (integerWaveNormSq_pos outputZero)
    have normLe :=
      wholeStateVelocityBilinearPairContribution_norm_le
        velocity velocity output pair.1 pair.2 rfl
          (velocityTransverse pair.1)
    have rhsNonneg :
        0 ≤
          (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityRowAmplitude velocity pair.1 *
            vorticityRowAmplitude velocity pair.2 := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg (by norm_num) Real.pi_pos.le
          · exact Real.sqrt_nonneg _
        · exact vorticityRowAmplitude_nonneg velocity pair.1
      · exact vorticityRowAmplitude_nonneg velocity pair.2
    have normSqLe :
        ‖wholeStateVelocityBilinearPairContribution
            velocity velocity pair‖ ^ 2 ≤
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityRowAmplitude velocity pair.1 *
            vorticityRowAmplitude velocity pair.2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mpr normLe
    rw [wholeVelocityPairNegativeOneDiagonalDensity]
    rw [if_neg outputZero]
    apply (div_le_iff₀ multiplierPos).2
    calc
      ‖wholeStateVelocityBilinearPairContribution
          velocity velocity pair‖ ^ 2 ≤
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityRowAmplitude velocity pair.1 *
            vorticityRowAmplitude velocity pair.2) ^ 2 :=
        normSqLe
      _ =
          (vorticityRowAmplitude velocity pair.1 ^ 2 *
            vorticityRowAmplitude velocity pair.2 ^ 2) *
            integerWaveViscousMultiplier output := by
        unfold integerWaveViscousMultiplier
        rw [show
          ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
              vorticityRowAmplitude velocity pair.1 *
              vorticityRowAmplitude velocity pair.2) ^ 2 =
            (2 * Real.pi) ^ 2 *
              Real.sqrt (integerWaveNormSq output) ^ 2 *
              vorticityRowAmplitude velocity pair.1 ^ 2 *
              vorticityRowAmplitude velocity pair.2 ^ 2 by
          ring]
        rw [Real.sq_sqrt (integerWaveNormSq_nonneg output)]
        ring

/-- Total pre-quotient diagonal mass over all ordered velocity input pairs. -/
def wholeVelocityPairNegativeOneDiagonalMass
    (velocity : ComplexVorticityHilbertState) : ℝ :=
  ∑' pair : IntegerWavevector × IntegerWavevector,
    wholeVelocityPairNegativeOneDiagonalDensity velocity pair

private theorem summable_velocityAmplitudeSqProduct
    (velocity : ComplexVorticityHilbertState) :
    Summable fun pair : IntegerWavevector × IntegerWavevector =>
      vorticityRowAmplitude velocity pair.1 ^ 2 *
        vorticityRowAmplitude velocity pair.2 ^ 2 := by
  have amplitudeSummable :
      Summable fun wave : IntegerWavevector =>
        vorticityRowAmplitude velocity wave ^ 2 :=
    summable_vorticityRowAmplitude_sq velocity
  have normSummable :
      Summable fun wave : IntegerWavevector =>
        ‖vorticityRowAmplitude velocity wave ^ 2‖ := by
    exact amplitudeSummable.congr fun wave => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact summable_mul_of_summable_norm normSummable normSummable

theorem summable_wholeVelocityPairNegativeOneDiagonalDensity
    (velocity : ComplexVorticityHilbertState)
    (velocityTransverse : WholeStateTransverse velocity) :
    Summable (wholeVelocityPairNegativeOneDiagonalDensity velocity) :=
  (summable_velocityAmplitudeSqProduct velocity).of_nonneg_of_le
    (wholeVelocityPairNegativeOneDiagonalDensity_nonneg velocity)
    (wholeVelocityPairNegativeOneDiagonalDensity_le
      velocity velocityTransverse)

/-- The complete ordered-pair diagonal costs at most the square of the whole
velocity mass.  Any larger fixed-output aggregate square must therefore come
from cross-pair interference rather than from unpaid individual
occurrences. -/
theorem wholeVelocityPairNegativeOneDiagonalMass_le
    (velocity : ComplexVorticityHilbertState)
    (velocityTransverse : WholeStateTransverse velocity) :
    wholeVelocityPairNegativeOneDiagonalMass velocity ≤
      wholeVorticityEuclideanMass velocity ^ 2 := by
  have amplitudeSummable :
      Summable fun wave : IntegerWavevector =>
        vorticityRowAmplitude velocity wave ^ 2 :=
    summable_vorticityRowAmplitude_sq velocity
  have productSummable :=
    summable_velocityAmplitudeSqProduct velocity
  calc
    wholeVelocityPairNegativeOneDiagonalMass velocity ≤
        ∑' pair : IntegerWavevector × IntegerWavevector,
          vorticityRowAmplitude velocity pair.1 ^ 2 *
            vorticityRowAmplitude velocity pair.2 ^ 2 := by
      unfold wholeVelocityPairNegativeOneDiagonalMass
      exact Summable.tsum_le_tsum
        (wholeVelocityPairNegativeOneDiagonalDensity_le
          velocity velocityTransverse)
        (summable_wholeVelocityPairNegativeOneDiagonalDensity
          velocity velocityTransverse)
        productSummable
    _ =
        (∑' wave : IntegerWavevector,
            vorticityRowAmplitude velocity wave ^ 2) *
          ∑' wave : IntegerWavevector,
            vorticityRowAmplitude velocity wave ^ 2 := by
      exact
        (amplitudeSummable.tsum_mul_tsum
          amplitudeSummable productSummable).symm
    _ = wholeVorticityEuclideanMass velocity ^ 2 := by
      unfold wholeVorticityEuclideanMass
      ring

/-- Actual physical specialization: the complete ordered velocity-pair
diagonal is paid by the square of the same vorticity state's kinetic mass.
The pair table, its transversality, and its positive budget are all generated
from `state`; no pair count or coercive constant is supplied. -/
theorem
    wholeVelocityPairNegativeOneDiagonalMass_wholeBiotSavartVelocityState_le
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    wholeVelocityPairNegativeOneDiagonalMass
        (wholeBiotSavartVelocityState state) ≤
      puncturedWholeVorticityKineticMass state ^ 2 := by
  rw [←
    wholeVorticityEuclideanMass_wholeBiotSavartVelocityState
      state transverse]
  exact
    wholeVelocityPairNegativeOneDiagonalMass_le
      (wholeBiotSavartVelocityState state)
      (wholeBiotSavartVelocityState_transverse state)

/-! ## Unweighted physical pair diagonal -/

/-- Euclidean square of one ordered velocity-convection occurrence generated
from a whole vorticity state.  The derivative remains on the transported
input, so this is the diagonal paid by kinetic mass times vorticity mass. -/
def wholeBiotSavartVelocityPairEuclideanDensity
    (state : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) : ℝ :=
  complexCoordinateAmplitudeSq
    (wholeStateVelocityBilinearPairContribution
      (wholeBiotSavartVelocityState state)
      (wholeBiotSavartVelocityState state) pair)

theorem wholeBiotSavartVelocityPairEuclideanDensity_nonneg
    (state : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    0 ≤ wholeBiotSavartVelocityPairEuclideanDensity state pair := by
  exact complexCoordinateAmplitudeSq_nonneg _

private theorem
    wholeStateVelocityBilinearPairContribution_amplitudeSq_le_second
    (left right : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) :
    complexCoordinateAmplitudeSq
        (wholeStateVelocityBilinearPairContribution
          left right (first, second)) ≤
      integerWaveViscousMultiplier second *
        complexCoordinateAmplitudeSq (left first) *
        complexCoordinateAmplitudeSq (right second) := by
  have dotBound :
      Complex.normSq (complexWavevector second ⬝ᵥ left first) ≤
        integerWaveNormSq second *
          complexCoordinateVectorNormSq (left first) := by
    simpa only [
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      (complexWavevector_dot_normSq_le second (left first))
  rw [wholeStateVelocityBilinearPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_neg, Complex.normSq_mul,
    Complex.normSq_I, Complex.normSq_ofReal, one_mul]
  simp only [
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  unfold integerWaveViscousMultiplier
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound (sq_nonneg (2 * Real.pi)))
      (complexCoordinateVectorNormSq_nonneg (right second))
  simpa only [pow_two, mul_assoc] using scaled

/-- One native velocity occurrence is paid by the kinetic row of its
advecting input and the vorticity row of its transported input. -/
theorem wholeBiotSavartVelocityPairEuclideanDensity_le
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state)
    (pair : IntegerWavevector × IntegerWavevector) :
    wholeBiotSavartVelocityPairEuclideanDensity state pair ≤
      complexCoordinateAmplitudeSq
          (wholeBiotSavartVelocityState state pair.1) *
        complexCoordinateAmplitudeSq (state pair.2) := by
  by_cases secondZero : pair.2 = 0
  · rw [show pair = (pair.1, 0) by ext <;> simp [secondZero]]
    simp [wholeBiotSavartVelocityPairEuclideanDensity,
      wholeBiotSavartVelocityState,
      wholeStateVelocityBilinearPairContribution,
      complexCoordinateAmplitudeSq]
    exact mul_nonneg
      (complexCoordinateAmplitudeSq_nonneg _)
      (complexCoordinateAmplitudeSq_nonneg _)
  · have occurrenceLe :=
      wholeStateVelocityBilinearPairContribution_amplitudeSq_le_second
        (wholeBiotSavartVelocityState state)
        (wholeBiotSavartVelocityState state) pair.1 pair.2
    have transportedIdentity :
        integerWaveViscousMultiplier pair.2 *
            complexCoordinateAmplitudeSq
              (wholeBiotSavartVelocityState state pair.2) =
          complexCoordinateAmplitudeSq (state pair.2) := by
      rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
        wholeBiotSavartVelocityState_apply,
        finiteStateVelocityCoefficient,
        biotSavartVelocityCoefficient_normSq_of_transverse
          pair.2 (state pair.2) secondZero (transverse pair.2),
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      unfold integerWaveViscousMultiplier
      field_simp [integerWaveNormSq_ne_zero secondZero,
        Real.pi_ne_zero]
    unfold wholeBiotSavartVelocityPairEuclideanDensity
    calc
      complexCoordinateAmplitudeSq
          (wholeStateVelocityBilinearPairContribution
            (wholeBiotSavartVelocityState state)
            (wholeBiotSavartVelocityState state) pair) ≤
          integerWaveViscousMultiplier pair.2 *
            complexCoordinateAmplitudeSq
              (wholeBiotSavartVelocityState state pair.1) *
            complexCoordinateAmplitudeSq
              (wholeBiotSavartVelocityState state pair.2) := occurrenceLe
      _ =
          complexCoordinateAmplitudeSq
              (wholeBiotSavartVelocityState state pair.1) *
            complexCoordinateAmplitudeSq (state pair.2) := by
        rw [← transportedIdentity]
        ring

/-- Complete unweighted diagonal of the physical velocity pair table. -/
def wholeBiotSavartVelocityPairEuclideanMass
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑' pair : IntegerWavevector × IntegerWavevector,
    wholeBiotSavartVelocityPairEuclideanDensity state pair

private theorem summable_biotSavartVelocity_vorticityAmplitudeProduct
    (state : ComplexVorticityHilbertState) :
    Summable fun pair : IntegerWavevector × IntegerWavevector =>
      complexCoordinateAmplitudeSq
          (wholeBiotSavartVelocityState state pair.1) *
        complexCoordinateAmplitudeSq (state pair.2) := by
  have velocitySummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq
          (wholeBiotSavartVelocityState state wave) := by
    exact
      (summable_vorticityRowAmplitude_sq
        (wholeBiotSavartVelocityState state)).congr fun wave => by
          rw [vorticityRowAmplitude_sq,
            ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have stateSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq (state wave) := by
    exact (summable_vorticityRowAmplitude_sq state).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have velocityNormSummable :=
    velocitySummable.norm
  have stateNormSummable := stateSummable.norm
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (complexCoordinateAmplitudeSq_nonneg _)] using
    summable_mul_of_summable_norm
      velocityNormSummable stateNormSummable

theorem summable_wholeBiotSavartVelocityPairEuclideanDensity
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    Summable (wholeBiotSavartVelocityPairEuclideanDensity state) :=
  (summable_biotSavartVelocity_vorticityAmplitudeProduct state)
    |>.of_nonneg_of_le
      (wholeBiotSavartVelocityPairEuclideanDensity_nonneg state)
      (wholeBiotSavartVelocityPairEuclideanDensity_le state transverse)

/-- The native unweighted pair diagonal is paid by the same state's kinetic
mass and complete vorticity mass. -/
theorem wholeBiotSavartVelocityPairEuclideanMass_le
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    wholeBiotSavartVelocityPairEuclideanMass state ≤
      puncturedWholeVorticityKineticMass state *
        wholeVorticityEuclideanMass state := by
  have velocitySummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq
          (wholeBiotSavartVelocityState state wave) := by
    exact
      (summable_vorticityRowAmplitude_sq
        (wholeBiotSavartVelocityState state)).congr fun wave => by
          rw [vorticityRowAmplitude_sq,
            ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have stateSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq (state wave) := by
    exact (summable_vorticityRowAmplitude_sq state).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have productSummable :=
    summable_biotSavartVelocity_vorticityAmplitudeProduct state
  calc
    wholeBiotSavartVelocityPairEuclideanMass state ≤
        ∑' pair : IntegerWavevector × IntegerWavevector,
          complexCoordinateAmplitudeSq
              (wholeBiotSavartVelocityState state pair.1) *
            complexCoordinateAmplitudeSq (state pair.2) := by
      unfold wholeBiotSavartVelocityPairEuclideanMass
      exact Summable.tsum_le_tsum
        (wholeBiotSavartVelocityPairEuclideanDensity_le state transverse)
        (summable_wholeBiotSavartVelocityPairEuclideanDensity
          state transverse)
        productSummable
    _ =
        (∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq
            (wholeBiotSavartVelocityState state wave)) *
          ∑' wave : IntegerWavevector,
            complexCoordinateAmplitudeSq (state wave) := by
      exact
        (velocitySummable.tsum_mul_tsum
          stateSummable productSummable).symm
    _ =
        wholeVorticityEuclideanMass
            (wholeBiotSavartVelocityState state) *
          wholeVorticityEuclideanMass state := by
      unfold wholeVorticityEuclideanMass
      congr 1 <;> apply tsum_congr <;> intro wave <;>
        rw [vorticityRowAmplitude_sq,
          ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    _ =
        puncturedWholeVorticityKineticMass state *
          wholeVorticityEuclideanMass state := by
      rw [wholeVorticityEuclideanMass_wholeBiotSavartVelocityState
        state transverse]

end

end ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
end NavierStokes
end SaturationMonoid
