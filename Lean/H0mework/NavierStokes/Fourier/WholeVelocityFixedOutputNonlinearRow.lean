import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow

/-!
# Whole-velocity fixed-output nonlinear Fourier rows

The kinetic Galerkin family is compactified on its velocity carrier, not on
the radius-growing vorticity carrier.  This module therefore forms the
velocity convection row directly on the existing whole `ℓ²` coefficient
space.  At one fixed output, transversality replaces the unbounded input
frequency by the fixed output frequency.  Discrete Cauchy--Schwarz then
gives absolute summability and a locally Lipschitz whole-carrier row.

The final finite-support theorem identifies this row with the actual
velocity convection already reconstructed from a finite vorticity state.
No critical enstrophy bound, cutoff, compactness witness, target limit, or
continuation premise is used.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow

open scoped BigOperators ENNReal Matrix Topology

open Filter Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

/-! ## Whole velocity convection before the Fourier quotient -/

/-- One ordered velocity-convection occurrence on the whole velocity
carrier.  Both arguments are already velocity states. -/
def wholeStateVelocityBilinearPairContribution
    (advecting transported : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    ComplexCoordinateVector :=
  -((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
      (complexWavevector pair.2 ⬝ᵥ
        advecting pair.1)) • transported pair.2

private theorem complexWavevector_add_local
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

private theorem second_dot_velocity_eq_output_dot
    (velocity : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse : complexWavevector first ⬝ᵥ velocity first = 0) :
    complexWavevector second ⬝ᵥ velocity first =
      complexWavevector output ⬝ᵥ velocity first := by
  rw [← incidence, complexWavevector_add_local,
    add_dotProduct, transverse]
  simp

private theorem wholeStateVelocityBilinearPairContribution_amplitudeSq_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse : complexWavevector first ⬝ᵥ left first = 0) :
    complexCoordinateAmplitudeSq
        (wholeStateVelocityBilinearPairContribution
          left right (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq (left first) *
        complexCoordinateAmplitudeSq (right second) := by
  have dotBound := complexWavevector_dot_normSq_le output (left first)
  rw [← second_dot_velocity_eq_output_dot
    left output first second incidence transverse] at dotBound
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [wholeStateVelocityBilinearPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_neg, Complex.normSq_mul,
    Complex.normSq_I, Complex.normSq_ofReal, one_mul]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound (sq_nonneg (2 * Real.pi)))
      (complexCoordinateVectorNormSq_nonneg (right second))
  simpa only [pow_two, mul_assoc] using scaled

/-- A whole velocity occurrence costs the fixed output frequency times the
two Euclidean row amplitudes; no ambient radius occurs. -/
theorem wholeStateVelocityBilinearPairContribution_norm_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse : complexWavevector first ⬝ᵥ left first = 0) :
    ‖wholeStateVelocityBilinearPairContribution
        left right (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        vorticityRowAmplitude left first *
        vorticityRowAmplitude right second := by
  have amplitudeLe :=
    wholeStateVelocityBilinearPairContribution_amplitudeSq_le
      left right output first second incidence transverse
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          vorticityRowAmplitude left first *
          vorticityRowAmplitude right second := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (vorticityRowAmplitude_nonneg left first))
      (vorticityRowAmplitude_nonneg right second)
  apply (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mp
  calc
    ‖wholeStateVelocityBilinearPairContribution
        left right (first, second)‖ ^ 2 ≤
      complexCoordinateAmplitudeSq
        (wholeStateVelocityBilinearPairContribution
          left right (first, second)) :=
      complexCoordinateVector_norm_sq_le_amplitudeSq _
    _ ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq (left first) *
        complexCoordinateAmplitudeSq (right second) := amplitudeLe
    _ =
      ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        vorticityRowAmplitude left first *
        vorticityRowAmplitude right second) ^ 2 := by
      symm
      simp only [
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      rw [mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (integerWaveNormSq_nonneg output),
        vorticityRowAmplitude_sq, vorticityRowAmplitude_sq]

/-! ## Absolutely summable whole rows -/

/-- Infinite bilinear velocity-convection row at one fixed output. -/
def wholeStateVelocityBilinearCoefficientAt
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  ∑' first : IntegerWavevector,
    wholeStateVelocityBilinearPairContribution
      left right (first, output - first)

theorem summable_norm_wholeStateVelocityBilinearPair
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      ‖wholeStateVelocityBilinearPairContribution
        left right (first, output - first)‖ := by
  let angular : ℝ :=
    (2 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  have productSummable :=
    summable_fixedOutputVorticityAmplitudeProduct left right output
  apply (productSummable.mul_left angular).of_nonneg_of_le
  · intro first
    exact norm_nonneg _
  · intro first
    have incidence : first + (output - first) = output := by
      abel
    simpa [angular, mul_assoc] using
      wholeStateVelocityBilinearPairContribution_norm_le
        left right output first (output - first)
        incidence (leftTransverse first)

theorem summable_wholeStateVelocityBilinearPair
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      wholeStateVelocityBilinearPairContribution
        left right (first, output - first) :=
  (summable_norm_wholeStateVelocityBilinearPair
    left right leftTransverse output).of_norm

theorem tsum_norm_wholeStateVelocityBilinearPair_le
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    (∑' first : IntegerWavevector,
        ‖wholeStateVelocityBilinearPairContribution
          left right (first, output - first)‖) ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        ‖left‖ * ‖right‖ := by
  let angular : ℝ :=
    (2 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  have angularNonneg : 0 ≤ angular := by
    dsimp [angular]
    positivity
  have normSummable :=
    summable_norm_wholeStateVelocityBilinearPair
      left right leftTransverse output
  have productSummable :=
    summable_fixedOutputVorticityAmplitudeProduct left right output
  calc
    (∑' first : IntegerWavevector,
        ‖wholeStateVelocityBilinearPairContribution
          left right (first, output - first)‖) ≤
      ∑' first : IntegerWavevector,
        angular *
          (vorticityRowAmplitude left first *
            vorticityRowAmplitude right (output - first)) := by
      exact Summable.tsum_le_tsum
        (fun first => by
          have incidence : first + (output - first) = output := by
            abel
          simpa [angular, mul_assoc] using
            wholeStateVelocityBilinearPairContribution_norm_le
              left right output first (output - first)
              incidence (leftTransverse first))
        normSummable (productSummable.mul_left angular)
    _ = angular *
        ∑' first : IntegerWavevector,
          vorticityRowAmplitude left first *
            vorticityRowAmplitude right (output - first) := by
      rw [tsum_mul_left]
    _ ≤ angular * (3 * ‖left‖ * ‖right‖) :=
      mul_le_mul_of_nonneg_left
        (tsum_fixedOutputVorticityAmplitudeProduct_le_three_mul_norm
          left right output)
        angularNonneg
    _ =
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        ‖left‖ * ‖right‖ := by
      dsimp [angular]
      ring

theorem wholeStateVelocityBilinearCoefficientAt_norm_le
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    ‖wholeStateVelocityBilinearCoefficientAt left right output‖ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        ‖left‖ * ‖right‖ := by
  have normSummable :=
    summable_norm_wholeStateVelocityBilinearPair
      left right leftTransverse output
  exact (norm_tsum_le_tsum_norm normSummable).trans
    (tsum_norm_wholeStateVelocityBilinearPair_le
      left right leftTransverse output)

/-! ## Quadratic row and local Lipschitz continuity -/

/-- Infinite quadratic velocity-convection row. -/
def wholeStateVelocityNonlinearCoefficientAt
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeStateVelocityBilinearCoefficientAt state state output

private theorem wholeStateVelocityBilinearPairContribution_sub_self
    (left right : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    wholeStateVelocityBilinearPairContribution left left pair -
        wholeStateVelocityBilinearPairContribution right right pair =
      wholeStateVelocityBilinearPairContribution
          (left - right) left pair +
        wholeStateVelocityBilinearPairContribution
          right (left - right) pair := by
  simp [wholeStateVelocityBilinearPairContribution,
    dotProduct_sub, smul_sub]
  module

theorem wholeStateVelocityNonlinearCoefficientAt_sub
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (output : IntegerWavevector) :
    wholeStateVelocityNonlinearCoefficientAt left output -
        wholeStateVelocityNonlinearCoefficientAt right output =
      wholeStateVelocityBilinearCoefficientAt
          (left - right) left output +
        wholeStateVelocityBilinearCoefficientAt
          right (left - right) output := by
  have leftSummable :=
    summable_wholeStateVelocityBilinearPair
      left left leftTransverse output
  have rightSummable :=
    summable_wholeStateVelocityBilinearPair
      right right rightTransverse output
  have differenceTransverse :=
    wholeStateTransverse_sub left right leftTransverse rightTransverse
  have firstBilinearSummable :=
    summable_wholeStateVelocityBilinearPair
      (left - right) left differenceTransverse output
  have secondBilinearSummable :=
    summable_wholeStateVelocityBilinearPair
      right (left - right) rightTransverse output
  unfold wholeStateVelocityNonlinearCoefficientAt
    wholeStateVelocityBilinearCoefficientAt
  rw [← leftSummable.tsum_sub rightSummable]
  rw [← firstBilinearSummable.tsum_add secondBilinearSummable]
  apply tsum_congr
  intro first
  exact wholeStateVelocityBilinearPairContribution_sub_self
    left right (first, output - first)

theorem wholeStateVelocityNonlinearCoefficientAt_sub_norm_le
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (output : IntegerWavevector) :
    ‖wholeStateVelocityNonlinearCoefficientAt left output -
        wholeStateVelocityNonlinearCoefficientAt right output‖ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        ‖left - right‖ * (‖left‖ + ‖right‖) := by
  rw [wholeStateVelocityNonlinearCoefficientAt_sub
    left right leftTransverse rightTransverse output]
  calc
    ‖wholeStateVelocityBilinearCoefficientAt
          (left - right) left output +
        wholeStateVelocityBilinearCoefficientAt
          right (left - right) output‖ ≤
      ‖wholeStateVelocityBilinearCoefficientAt
          (left - right) left output‖ +
        ‖wholeStateVelocityBilinearCoefficientAt
          right (left - right) output‖ := norm_add_le _ _
    _ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            ‖left - right‖ * ‖left‖ +
        (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            ‖right‖ * ‖left - right‖ :=
      add_le_add
        (wholeStateVelocityBilinearCoefficientAt_norm_le
          (left - right) left
          (wholeStateTransverse_sub
            left right leftTransverse rightTransverse)
          output)
        (wholeStateVelocityBilinearCoefficientAt_norm_le
          right (left - right) rightTransverse output)
    _ =
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        ‖left - right‖ * (‖left‖ + ‖right‖) := by
      ring

/-- The whole transverse velocity carrier is the genuine domain of the
fixed-output convection observer. -/
abbrev WholeTransverseVelocityState :=
  {state : ComplexVorticityHilbertState //
    WholeStateTransverse state}

theorem tendsto_wholeStateVelocityNonlinearCoefficientAt
    {α : Type*}
    {filter : Filter α}
    (states : α → ComplexVorticityHilbertState)
    (limit : ComplexVorticityHilbertState)
    (statesTransverse :
      ∀ index, WholeStateTransverse (states index))
    (limitTransverse : WholeStateTransverse limit)
    (statesTendsto : Filter.Tendsto states filter (nhds limit))
    (output : IntegerWavevector) :
    Filter.Tendsto
      (fun index =>
        wholeStateVelocityNonlinearCoefficientAt
          (states index) output)
      filter
      (nhds
        (wholeStateVelocityNonlinearCoefficientAt
          limit output)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  let angular : ℝ :=
    (6 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  have differenceNormTends :
      Filter.Tendsto
        (fun index => ‖states index - limit‖)
        filter (nhds 0) := by
    simpa using
      (statesTendsto.sub
        (tendsto_const_nhds :
          Filter.Tendsto
            (fun _ : α => limit) filter (nhds limit))).norm
  have stateNormSumTends :
      Filter.Tendsto
        (fun index => ‖states index‖ + ‖limit‖)
        filter (nhds (‖limit‖ + ‖limit‖)) :=
    statesTendsto.norm.add tendsto_const_nhds
  have boundTends :
      Filter.Tendsto
        (fun index =>
          angular * ‖states index - limit‖ *
            (‖states index‖ + ‖limit‖))
        filter (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul differenceNormTends).mul
        stateNormSumTends)
  exact squeeze_zero
    (g := fun index =>
      angular * ‖states index - limit‖ *
        (‖states index‖ + ‖limit‖))
    (fun _ => dist_nonneg)
    (fun index => by
      rw [dist_eq_norm]
      simpa [angular] using
        wholeStateVelocityNonlinearCoefficientAt_sub_norm_le
          (states index) limit
          (statesTransverse index) limitTransverse output)
    boundTends

theorem wholeStateVelocityNonlinearCoefficientAt_continuous
    (output : IntegerWavevector) :
    Continuous
      (fun state : WholeTransverseVelocityState =>
        wholeStateVelocityNonlinearCoefficientAt
          state.1 output) := by
  rw [continuous_iff_continuousAt]
  intro state
  exact
    tendsto_wholeStateVelocityNonlinearCoefficientAt
      (fun later : WholeTransverseVelocityState => later.1)
      state.1 (fun later => later.2) state.2
      continuousAt_subtype_val output

/-! ## Exact agreement with the actual finite Galerkin row -/

/-- The velocity read from a finite vorticity state, installed on the same
whole carrier used by compactness. -/
def finiteStateWholeVelocity
    (modes : Finset IntegerWavevector)
    (vorticity : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes
    (finiteStateVelocityCoefficient vorticity)

@[simp] theorem finiteStateWholeVelocity_apply
    (modes : Finset IntegerWavevector)
    (vorticity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    finiteStateWholeVelocity modes vorticity wave =
      if wave ∈ modes then
        finiteStateVelocityCoefficient vorticity wave
      else 0 := by
  simp [finiteStateWholeVelocity]

theorem finiteStateWholeVelocity_transverse
    (modes : Finset IntegerWavevector)
    (vorticity : ComplexVorticityHilbertState) :
    WholeStateTransverse
      (finiteStateWholeVelocity modes vorticity) := by
  intro wave
  by_cases waveMem : wave ∈ modes
  · rw [finiteStateWholeVelocity_apply, if_pos waveMem]
    unfold finiteStateVelocityCoefficient
    exact complexWavevector_dot_biotSavartVelocityCoefficient _ _
  · simp [finiteStateWholeVelocity_apply, waveMem]

private theorem finiteStateVelocityNonlinearCoefficientAt_eq_reducedSum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVelocityNonlinearCoefficientAt modes state output =
      ∑ first ∈ modes,
        if output - first ∈ modes then
          finiteStateVelocityNonlinearPairContribution
            state (first, output - first)
        else 0 := by
  unfold finiteStateVelocityNonlinearCoefficientAt
  apply Finset.sum_congr rfl
  intro first firstMem
  have condition :
      ∀ second : IntegerWavevector,
        first + second = output ↔ second = output - first := by
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

/-- The whole velocity row is exactly the already-generated finite
Galerkin convection row on the installed finite velocity state. -/
theorem wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity
    (modes : Finset IntegerWavevector)
    (vorticity : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeStateVelocityNonlinearCoefficientAt
        (finiteStateWholeVelocity modes vorticity) output =
      finiteStateVelocityNonlinearCoefficientAt
        modes vorticity output := by
  rw [wholeStateVelocityNonlinearCoefficientAt,
    wholeStateVelocityBilinearCoefficientAt,
    tsum_eq_sum (s := modes)]
  · rw [finiteStateVelocityNonlinearCoefficientAt_eq_reducedSum]
    apply Finset.sum_congr rfl
    intro first firstMem
    by_cases translatedMem : output - first ∈ modes
    · simp [translatedMem,
        wholeStateVelocityBilinearPairContribution,
        finiteStateVelocityNonlinearPairContribution,
        finiteStateWholeVelocity_apply, firstMem]
    · simp [translatedMem,
        wholeStateVelocityBilinearPairContribution,
        finiteStateWholeVelocity_apply, firstMem]
  · intro first firstNotMem
    simp [wholeStateVelocityBilinearPairContribution,
      finiteStateWholeVelocity_apply, firstNotMem]

end

end ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
end NavierStokes
end SaturationMonoid
