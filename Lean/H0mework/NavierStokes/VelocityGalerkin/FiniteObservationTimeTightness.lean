import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import H0mework.NavierStokes.Fourier.FixedOutputNonlinearContinuity
import H0mework.NavierStokes.ShellSources.WholeEnstrophyIdentity
import H0mework.NavierStokes.VelocityGalerkin.UniformKineticLedger

/-!
# Cutoff-independent time tightness of fixed velocity observations

The source-generated endpoint family carries a radius-uniform kinetic
ledger.  Before any compactness quotient, one fixed velocity Fourier row of
the actual Galerkin update has a speed bounded only by the endpoint kinetic
norm, viscosity, and that fixed output wave.  Discrete Cauchy--Schwarz at a
fixed output removes the ambient mode count.

Consequently every retained fixed velocity row is Lipschitz on `[0,1]` with
one radius-independent modulus.  No cutoff, target path, convergence
witness, critical margin, or continuation certificate enters the theorem
mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness

open scoped BigOperators Interval Matrix Topology

open Set Filter MeasureTheory Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger

noncomputable section

/-! ## Contractivity of the physical row projection -/

/-- The rowwise Leray projection is contractive in the Euclidean
coefficient square.  This is proved from the already generated
curl/Biot--Savart square rather than installed as an observer premise. -/
theorem transverseProjection_amplitudeSq_le
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (transverseProjection wave vector) ≤
      complexCoordinateAmplitudeSq vector := by
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [← biotSavartVelocityCoefficient_fourierCurlCoefficient
    wave vector waveNe]
  have biotSavartBound :=
    biotSavartVelocityCoefficient_normSq_le
      wave (fourierCurlCoefficient wave vector) waveNe
  have crossBound := complexWavevector_cross_normSq_le wave vector
  have denominatorPos :
      0 < (2 * Real.pi) ^ 2 * integerWaveNormSq wave := by
    exact mul_pos (sq_pos_of_pos (by positivity))
      (integerWaveNormSq_pos waveNe)
  have curlBound :
      complexCoordinateVectorNormSq
          (fourierCurlCoefficient wave vector) ≤
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) *
          complexCoordinateVectorNormSq vector := by
    rw [fourierCurlCoefficient,
      complexCoordinateVectorNormSq_smul,
      Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_ofReal, one_mul]
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_left crossBound (sq_nonneg (2 * Real.pi))
  calc
    complexCoordinateVectorNormSq
        (biotSavartVelocityCoefficient wave
          (fourierCurlCoefficient wave vector)) ≤
      complexCoordinateVectorNormSq
          (fourierCurlCoefficient wave vector) /
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) :=
      biotSavartBound
    _ ≤
      (((2 * Real.pi) ^ 2 * integerWaveNormSq wave) *
          complexCoordinateVectorNormSq vector) /
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) :=
      div_le_div_of_nonneg_right curlBound denominatorPos.le
    _ = complexCoordinateVectorNormSq vector := by
      exact mul_div_cancel_left₀ _ denominatorPos.ne'

/-! ## Fixed-output velocity convolution -/

/-- Velocity-amplitude convolution at one fixed output.  Incidence fixes
the second input as `output - first`. -/
def fixedOutputVelocityConvolutionAmplitude
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ℝ :=
  ∑ first ∈ modes,
    if output - first ∈ modes then
      velocityRowAmplitude state first *
        velocityRowAmplitude state (output - first)
    else 0

private theorem doubleIncidenceVelocityAmplitude_eq_fixedOutput
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          velocityRowAmplitude state first *
            velocityRowAmplitude state second
        else 0) =
      fixedOutputVelocityConvolutionAmplitude modes state output := by
  unfold fixedOutputVelocityConvolutionAmplitude
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

private theorem translated_velocityRowAmplitude_sq_sum_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ modes,
        if output - first ∈ modes then
          velocityRowAmplitude state (output - first) ^ 2
        else 0) ≤
      ∑ second ∈ modes,
        velocityRowAmplitude state second ^ 2 := by
  let translated : Finset IntegerWavevector :=
    modes.image fun second => output - second
  have filteredSubset :
      modes.filter (fun first => output - first ∈ modes) ⊆
        translated := by
    intro first firstMem
    have membership := Finset.mem_filter.mp firstMem
    apply Finset.mem_image.mpr
    refine ⟨output - first, membership.2, ?_⟩
    abel
  have translatedSum :
      (∑ first ∈ translated,
          velocityRowAmplitude state (output - first) ^ 2) =
        ∑ second ∈ modes,
          velocityRowAmplitude state second ^ 2 := by
    dsimp [translated]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro second secondMem
      congr 2
      abel
    · intro left leftMem right rightMem equality
      exact sub_right_inj.mp equality
  rw [← Finset.sum_filter]
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg
      filteredSubset
      (fun first firstMem firstNotMem =>
        sq_nonneg (velocityRowAmplitude state (output - first)))).trans_eq
      translatedSum

theorem velocityRowAmplitude_sq_sum_eq_two_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes, velocityRowAmplitude state wave ^ 2) =
      2 * finiteStateVorticityKineticEnergy modes state := by
  unfold finiteStateVorticityKineticEnergy
  have rowIdentity :
      (∑ wave ∈ modes, velocityRowAmplitude state wave ^ 2) =
        ∑ wave ∈ modes,
          complexCoordinateVectorNormSq
            (finiteStateVelocityCoefficient state wave) := by
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [velocityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [rowIdentity]
  ring

/-- Fixed-output velocity convolution is paid by twice the actual kinetic
energy, uniformly in the ambient finite carrier. -/
theorem fixedOutputVelocityConvolutionAmplitude_le_two_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    fixedOutputVelocityConvolutionAmplitude modes state output ≤
      2 * finiteStateVorticityKineticEnergy modes state := by
  let translatedAmplitude : IntegerWavevector → ℝ :=
    fun first =>
      if output - first ∈ modes then
        velocityRowAmplitude state (output - first)
      else 0
  have cauchy :=
    Real.sum_mul_le_sqrt_mul_sqrt
      modes (velocityRowAmplitude state) translatedAmplitude
  have translatedSqLe :
      (∑ first ∈ modes, translatedAmplitude first ^ 2) ≤
        ∑ second ∈ modes,
          velocityRowAmplitude state second ^ 2 := by
    dsimp [translatedAmplitude]
    calc
      (∑ first ∈ modes,
          (if output - first ∈ modes then
              velocityRowAmplitude state (output - first)
            else 0) ^ 2) =
          ∑ first ∈ modes,
            if output - first ∈ modes then
              velocityRowAmplitude state (output - first) ^ 2
            else 0 := by
        apply Finset.sum_congr rfl
        intro first firstMem
        by_cases translatedMem : output - first ∈ modes <;>
          simp [translatedMem]
      _ ≤
          ∑ second ∈ modes,
            velocityRowAmplitude state second ^ 2 :=
        translated_velocityRowAmplitude_sq_sum_le modes state output
  have sqrtTranslatedLe := Real.sqrt_le_sqrt translatedSqLe
  have squareSumNonneg :
      0 ≤ ∑ wave ∈ modes,
        velocityRowAmplitude state wave ^ 2 :=
    Finset.sum_nonneg fun wave waveMem => sq_nonneg _
  calc
    fixedOutputVelocityConvolutionAmplitude modes state output =
        ∑ first ∈ modes,
          velocityRowAmplitude state first * translatedAmplitude first := by
      unfold fixedOutputVelocityConvolutionAmplitude
      apply Finset.sum_congr rfl
      intro first firstMem
      by_cases translatedMem : output - first ∈ modes <;>
        simp [translatedAmplitude, translatedMem]
    _ ≤
        Real.sqrt
            (∑ first ∈ modes,
              velocityRowAmplitude state first ^ 2) *
          Real.sqrt
            (∑ first ∈ modes,
              translatedAmplitude first ^ 2) := cauchy
    _ ≤
        Real.sqrt
            (∑ first ∈ modes,
              velocityRowAmplitude state first ^ 2) *
          Real.sqrt
            (∑ second ∈ modes,
              velocityRowAmplitude state second ^ 2) :=
      mul_le_mul_of_nonneg_left sqrtTranslatedLe (Real.sqrt_nonneg _)
    _ = ∑ wave ∈ modes,
          velocityRowAmplitude state wave ^ 2 := by
      exact Real.mul_self_sqrt squareSumNonneg
    _ = 2 * finiteStateVorticityKineticEnergy modes state :=
      velocityRowAmplitude_sq_sum_eq_two_kineticEnergy modes state

/-! ## Fixed velocity row of the actual update -/

private theorem complexWavevector_add_local
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

private theorem second_dot_velocity_eq_output_dot
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexWavevector second ⬝ᵥ
        finiteStateVelocityCoefficient state first =
      complexWavevector output ⬝ᵥ
        finiteStateVelocityCoefficient state first := by
  have velocityTransverse :
      complexWavevector first ⬝ᵥ
          finiteStateVelocityCoefficient state first = 0 := by
    unfold finiteStateVelocityCoefficient
    exact complexWavevector_dot_biotSavartVelocityCoefficient first _
  rw [← incidence, complexWavevector_add_local,
    add_dotProduct, velocityTransverse]
  simp

private theorem finiteStateVelocityNonlinearPairContribution_amplitudeSq_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexCoordinateAmplitudeSq
        (finiteStateVelocityNonlinearPairContribution state (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state first) *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le
      output (finiteStateVelocityCoefficient state first)
  rw [← second_dot_velocity_eq_output_dot
    state output first second incidence] at dotBound
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVelocityNonlinearPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_neg, Complex.normSq_mul,
    Complex.normSq_I, Complex.normSq_ofReal, one_mul]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound (sq_nonneg (2 * Real.pi)))
      (complexCoordinateVectorNormSq_nonneg
        (finiteStateVelocityCoefficient state second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem finiteStateVelocityNonlinearPairContribution_norm_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    ‖finiteStateVelocityNonlinearPairContribution state (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        velocityRowAmplitude state first *
        velocityRowAmplitude state second := by
  have amplitudeLe :=
    finiteStateVelocityNonlinearPairContribution_amplitudeSq_le
      state output first second incidence
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          velocityRowAmplitude state first *
          velocityRowAmplitude state second := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)
          (Real.sqrt_nonneg _))
        (velocityRowAmplitude_nonneg state first))
      (velocityRowAmplitude_nonneg state second)
  apply (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mp
  calc
    ‖finiteStateVelocityNonlinearPairContribution
        state (first, second)‖ ^ 2 ≤
      complexCoordinateAmplitudeSq
        (finiteStateVelocityNonlinearPairContribution state (first, second)) :=
      complexCoordinateVector_norm_sq_le_amplitudeSq _
    _ ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state first) *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state second) := amplitudeLe
    _ =
      ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        velocityRowAmplitude state first *
        velocityRowAmplitude state second) ^ 2 := by
      symm
      rw [mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (integerWaveNormSq_nonneg output),
        velocityRowAmplitude_sq, velocityRowAmplitude_sq]

/-- One fixed velocity convection row is bounded by the same-time kinetic
energy, with no mode-count or maximal-frequency loss. -/
theorem finiteStateVelocityNonlinearCoefficientAt_norm_le_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    ‖finiteStateVelocityNonlinearCoefficientAt modes state output‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        (2 * finiteStateVorticityKineticEnergy modes state) := by
  let angular : ℝ :=
    (2 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  have aggregateNorm :
      ‖finiteStateVelocityNonlinearCoefficientAt modes state output‖ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVelocityNonlinearPairContribution
                  state (first, second)
              else 0‖ := by
    unfold finiteStateVelocityNonlinearCoefficientAt
    exact
      (norm_sum_le modes fun first =>
        ∑ second ∈ modes,
          if first + second = output then
            finiteStateVelocityNonlinearPairContribution state (first, second)
          else 0).trans
        (Finset.sum_le_sum fun first firstMem =>
          norm_sum_le modes fun second =>
            if first + second = output then
              finiteStateVelocityNonlinearPairContribution state (first, second)
            else 0)
  have pairwiseNorm :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVelocityNonlinearPairContribution
                  state (first, second)
              else 0‖) ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (velocityRowAmplitude state first *
                  velocityRowAmplitude state second)
            else 0 := by
    apply Finset.sum_le_sum
    intro first firstMem
    apply Finset.sum_le_sum
    intro second secondMem
    by_cases incidence : first + second = output
    · simp only [if_pos incidence]
      simpa [angular, mul_assoc] using
        finiteStateVelocityNonlinearPairContribution_norm_le
          state output first second incidence
    · simp [incidence]
  have factorAngular :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (velocityRowAmplitude state first *
                  velocityRowAmplitude state second)
            else 0) =
        angular * fixedOutputVelocityConvolutionAmplitude
          modes state output := by
    rw [← doubleIncidenceVelocityAmplitude_eq_fixedOutput]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first firstMem
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases incidence : first + second = output <;> simp [incidence]
  calc
    ‖finiteStateVelocityNonlinearCoefficientAt modes state output‖ ≤
      angular * fixedOutputVelocityConvolutionAmplitude modes state output :=
        aggregateNorm.trans (pairwiseNorm.trans_eq factorAngular)
    _ ≤ angular * (2 * finiteStateVorticityKineticEnergy modes state) :=
      mul_le_mul_of_nonneg_left
        (fixedOutputVelocityConvolutionAmplitude_le_two_kineticEnergy
          modes state output)
        (by positivity)
    _ = _ := rfl

/-- On a retained nonzero row, Biot--Savart transports the actual
vorticity generator to the Leray-projected velocity convection minus the
viscous velocity row. -/
private theorem biotSavartVelocityCoefficient_real_smul
    (wave : IntegerWavevector)
    (scalar : ℝ)
    (vorticity : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient wave (scalar • vorticity) =
      scalar • biotSavartVelocityCoefficient wave vorticity := by
  change
    biotSavartVelocityCoefficient wave ((scalar : ℂ) • vorticity) =
      (scalar : ℂ) • biotSavartVelocityCoefficient wave vorticity
  exact biotSavartVelocityCoefficient_smul wave scalar vorticity

theorem biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (nu : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector)
    (outputMem : output ∈ modes) :
    biotSavartVelocityCoefficient output
        (finiteStateVorticityGenerator modes nu state output) =
      transverseProjection output
          (finiteStateVelocityNonlinearCoefficientAt modes state output) -
        (nu * integerWaveViscousMultiplier output) •
          finiteStateVelocityCoefficient state output := by
  have outputNe : output ≠ 0 := fun outputZero =>
    zeroNotMem (outputZero ▸ outputMem)
  rw [finiteStateVorticityGenerator_apply, if_pos outputMem,
    biotSavartVelocityCoefficient_sub,
    finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
      modes zeroNotMem state stateTransverse output,
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      output (finiteStateVelocityNonlinearCoefficientAt modes state output)
      outputNe,
    biotSavartVelocityCoefficient_real_smul]
  rfl

/-- Source-generated cutoff-independent speed bound for one retained
velocity Fourier row. -/
theorem generatedVelocityEndpointGalerkinWave_speed_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1)
    (output : IntegerWavevector)
    (outputMem : output ∈ wholeRestartModes radius) :
    ‖biotSavartVelocityCoefficient output
        (finiteStateVorticityGenerator
          (wholeRestartModes radius) nu.coeff
          ((ledger.family.stage radius).trajectory time.1) output)‖ ≤
      3 * (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 +
        nu.coeff * integerWaveViscousMultiplier output *
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  let stage := ledger.family.stage radius
  let state := stage.trajectory time.1
  let endpointNorm := ‖ledger.family.endpointReceipt.velocityEndpoint‖
  have physical := stage.physical time.1 time.2
  have outputNe : output ≠ 0 := fun outputZero =>
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
      (outputZero ▸ outputMem)
  rw [biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
    (wholeRestartModes radius)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
    nu.coeff state
    (fun wave waveMem => physical.2.2.1 wave)
    output outputMem]
  calc
    ‖transverseProjection output
          (finiteStateVelocityNonlinearCoefficientAt
            (wholeRestartModes radius) state output) -
        (nu.coeff * integerWaveViscousMultiplier output) •
          finiteStateVelocityCoefficient state output‖ ≤
      ‖transverseProjection output
          (finiteStateVelocityNonlinearCoefficientAt
            (wholeRestartModes radius) state output)‖ +
        ‖(nu.coeff * integerWaveViscousMultiplier output) •
          finiteStateVelocityCoefficient state output‖ := norm_sub_le _ _
    _ ≤
      3 * (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (2 * finiteStateVorticityKineticEnergy
            (wholeRestartModes radius) state) +
        (nu.coeff * integerWaveViscousMultiplier output) *
          Real.sqrt
            (complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient state output)) := by
      apply add_le_add
      · have projectionSqLe :=
          transverseProjection_amplitudeSq_le output outputNe
            (finiteStateVelocityNonlinearCoefficientAt
              (wholeRestartModes radius) state output)
        let nonlinear :=
          finiteStateVelocityNonlinearCoefficientAt
            (wholeRestartModes radius) state output
        have projectionAmbientSqLe :
            ‖transverseProjection output nonlinear‖ ^ 2 ≤
              3 * ‖nonlinear‖ ^ 2 := by
          exact
            (complexCoordinateVector_norm_sq_le_amplitudeSq
              (transverseProjection output nonlinear)).trans
              (projectionSqLe.trans
                (ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity.complexCoordinateAmplitudeSq_le_three_mul_norm_sq
                  nonlinear))
        have projectionNormLe :
            ‖transverseProjection output nonlinear‖ ≤
              3 * ‖nonlinear‖ := by
          have leftNonneg := norm_nonneg (transverseProjection output nonlinear)
          have rightNonneg : 0 ≤ 3 * ‖nonlinear‖ := by positivity
          apply (sq_le_sq₀ leftNonneg rightNonneg).mp
          nlinarith [sq_nonneg ‖nonlinear‖]
        have nonlinearBound :=
          finiteStateVelocityNonlinearCoefficientAt_norm_le_kineticEnergy
            (wholeRestartModes radius) state output
        exact projectionNormLe.trans (by
          calc
            3 * ‖nonlinear‖ ≤
                3 * ((2 * Real.pi) *
                  Real.sqrt (integerWaveNormSq output) *
                  (2 * finiteStateVorticityKineticEnergy
                    (wholeRestartModes radius) state)) :=
              mul_le_mul_of_nonneg_left nonlinearBound (by norm_num)
            _ = _ := by ring)
      · rw [norm_smul]
        have coefficientNonneg :
            0 ≤ nu.coeff * integerWaveViscousMultiplier output :=
          mul_nonneg nu.coeff_pos.le
            (mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg output))
        rw [Real.norm_eq_abs, abs_of_nonneg coefficientNonneg]
        exact mul_le_mul_of_nonneg_left
          (Real.le_sqrt_of_sq_le
            (complexCoordinateVector_norm_sq_le_amplitudeSq _))
          coefficientNonneg
    _ ≤
      3 * (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          endpointNorm ^ 2 +
        nu.coeff * integerWaveViscousMultiplier output * endpointNorm := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (by nlinarith [ledger.kinetic_energy_le radius time])
          (by positivity)
      · apply mul_le_mul_of_nonneg_left
        · have rowSqLeEnergy :
              complexCoordinateAmplitudeSq
                    (finiteStateVelocityCoefficient state output) ≤
                2 * finiteStateVorticityKineticEnergy
                  (wholeRestartModes radius) state := by
            rw [← velocityRowAmplitude_sq]
            rw [← velocityRowAmplitude_sq_sum_eq_two_kineticEnergy]
            exact Finset.single_le_sum
              (fun wave waveMem => sq_nonneg (velocityRowAmplitude state wave))
              outputMem
          have rowSqLeEndpoint :
              complexCoordinateAmplitudeSq
                    (finiteStateVelocityCoefficient state output) ≤
                endpointNorm ^ 2 :=
            rowSqLeEnergy.trans (by nlinarith [ledger.kinetic_energy_le radius time])
          have amplitudeNonneg :=
            complexCoordinateAmplitudeSq_nonneg
              (finiteStateVelocityCoefficient state output)
          apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
          rw [Real.sq_sqrt amplitudeNonneg]
          simpa [endpointNorm] using rowSqLeEndpoint
        · exact mul_nonneg nu.coeff_pos.le
            (mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg output))
    _ = _ := rfl

/-! ## Radius-independent time modulus -/

/-- The speed ceiling generated by the physical endpoint, viscosity, and
one observed wave.  It contains no Galerkin radius. -/
def generatedVelocityEndpointGalerkinWaveSpeedCeiling
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (output : IntegerWavevector) : ℝ :=
  3 * (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 +
    nu.coeff * integerWaveViscousMultiplier output *
      ‖ledger.family.endpointReceipt.velocityEndpoint‖

theorem generatedVelocityEndpointGalerkinWaveSpeedCeiling_nonneg
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (output : IntegerWavevector) :
    0 ≤ generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger output := by
  unfold generatedVelocityEndpointGalerkinWaveSpeedCeiling
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output)
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg (by norm_num) Real.pi_pos.le))
        (Real.sqrt_nonneg _))
      (sq_nonneg _)
  · exact mul_nonneg
      (mul_nonneg nu.coeff_pos.le multiplierNonneg)
      (norm_nonneg _)

/-- The actual velocity coefficient path at one generated radius and one
fixed output wave. -/
def generatedVelocityEndpointGalerkinWavePath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector) :
    Icc (0 : ℝ) 1 → ComplexCoordinateVector :=
  fun time =>
    finiteStateVelocityCoefficient
      ((ledger.family.stage radius).trajectory time.1) output

/-- Every retained fixed velocity row of the source-generated canonical
family has the same Lipschitz modulus, independently of the radius. -/
theorem generatedVelocityEndpointGalerkinWavePath_increment_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector)
    (outputMem : output ∈ wholeRestartModes radius)
    (first second : Icc (0 : ℝ) 1) :
    ‖generatedVelocityEndpointGalerkinWavePath
          ledger radius output second -
        generatedVelocityEndpointGalerkinWavePath
          ledger radius output first‖ ≤
      generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger output *
        ‖(second.1 - first.1 : ℝ)‖ := by
  let stage := ledger.family.stage radius
  let path : ℝ → ComplexCoordinateVector := fun time =>
    finiteStateVelocityCoefficient (stage.trajectory time) output
  let tangent : ℝ → ComplexCoordinateVector := fun time =>
    biotSavartVelocityCoefficient output
      (finiteStateVorticityGenerator
        (wholeRestartModes radius) nu.coeff
        (stage.trajectory time) output)
  have pathDerivative :
      ∀ time ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path (tangent time) (Icc (0 : ℝ) 1) time := by
    intro time timeMem
    exact
      (finiteStateVelocityTrajectoryWave_hasDerivAt
        stage.trajectory time
        (finiteStateVorticityGenerator
          (wholeRestartModes radius) nu.coeff
          (stage.trajectory time))
        output (stage.physical time timeMem).1).hasDerivWithinAt
  have tangentBound :
      ∀ time ∈ Icc (0 : ℝ) 1,
        ‖tangent time‖ ≤
          generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger output := by
    intro time timeMem
    exact generatedVelocityEndpointGalerkinWave_speed_le
      ledger radius ⟨time, timeMem⟩ output outputMem
  have increment :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      pathDerivative tangentBound (convex_Icc (0 : ℝ) 1)
      first.2 second.2
  simpa [path, tangent, generatedVelocityEndpointGalerkinWavePath] using
    increment

/-- Distance form of the same radius-independent modulus. -/
theorem generatedVelocityEndpointGalerkinWavePath_dist_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector)
    (outputMem : output ∈ wholeRestartModes radius)
    (first second : Icc (0 : ℝ) 1) :
    dist
        (generatedVelocityEndpointGalerkinWavePath
          ledger radius output first)
        (generatedVelocityEndpointGalerkinWavePath
          ledger radius output second) ≤
      generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger output *
        dist first second := by
  have increment :=
    generatedVelocityEndpointGalerkinWavePath_increment_le
      ledger radius output outputMem second first
  simpa only [Subtype.dist_eq, dist_eq_norm] using increment

/-- The same modulus holds at every radius.  Before the observed wave enters
the canonical punctured cube its actual Galerkin row is identically zero. -/
theorem generatedVelocityEndpointGalerkinWavePath_dist_le_allRadius
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector)
    (first second : Icc (0 : ℝ) 1) :
    dist
        (generatedVelocityEndpointGalerkinWavePath
          ledger radius output first)
        (generatedVelocityEndpointGalerkinWavePath
          ledger radius output second) ≤
      generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger output *
        dist first second := by
  by_cases outputMem : output ∈ wholeRestartModes radius
  · exact generatedVelocityEndpointGalerkinWavePath_dist_le
      ledger radius output outputMem first second
  · have firstZero :
        (ledger.family.stage radius).trajectory first.1 output = 0 :=
      (ledger.family.stage radius).physical first.1 first.2 |>.2.1
        output outputMem
    have secondZero :
        (ledger.family.stage radius).trajectory second.1 output = 0 :=
      (ledger.family.stage radius).physical second.1 second.2 |>.2.1
        output outputMem
    simp [generatedVelocityEndpointGalerkinWavePath,
      finiteStateVelocityCoefficient, firstZero, secondZero]
    exact mul_nonneg
      (generatedVelocityEndpointGalerkinWaveSpeedCeiling_nonneg ledger output)
      dist_nonneg

/-- Every fixed velocity row is bounded by the complete endpoint norm at
every radius and physical time. -/
theorem generatedVelocityEndpointGalerkinWavePath_norm_le_endpoint
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) 1) :
    ‖generatedVelocityEndpointGalerkinWavePath
        ledger radius output time‖ ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  let state := (ledger.family.stage radius).trajectory time.1
  by_cases outputMem : output ∈ wholeRestartModes radius
  · have rowAmplitudeLeEnergy :
        complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient state output) ≤
          2 * finiteStateVorticityKineticEnergy
            (wholeRestartModes radius) state := by
      rw [← velocityRowAmplitude_sq]
      rw [← velocityRowAmplitude_sq_sum_eq_two_kineticEnergy]
      exact Finset.single_le_sum
        (fun wave waveMem => sq_nonneg (velocityRowAmplitude state wave))
        outputMem
    have rowAmplitudeLeEndpoint :
        complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient state output) ≤
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 :=
      rowAmplitudeLeEnergy.trans
        (by nlinarith [ledger.kinetic_energy_le radius time])
    have rowNormSqLeEndpoint :
        ‖finiteStateVelocityCoefficient state output‖ ^ 2 ≤
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 :=
      (complexCoordinateVector_norm_sq_le_amplitudeSq _).trans
        rowAmplitudeLeEndpoint
    simpa [generatedVelocityEndpointGalerkinWavePath, state] using
      (sq_le_sq₀
        (norm_nonneg (finiteStateVelocityCoefficient state output))
        (norm_nonneg ledger.family.endpointReceipt.velocityEndpoint)).mp
        rowNormSqLeEndpoint
  · have rowZero : state output = 0 :=
      (ledger.family.stage radius).physical time.1 time.2 |>.2.1
        output outputMem
    simp [generatedVelocityEndpointGalerkinWavePath, state,
      finiteStateVelocityCoefficient, rowZero]

/-! ## Arbitrary fixed finite observations -/

/-- Velocity rows retained by one arbitrary finite observation inventory. -/
abbrev FiniteObservedVelocityState
    (observed : Finset IntegerWavevector) :=
  {wave : IntegerWavevector // wave ∈ observed} →
    ComplexCoordinateVector

/-- Read an arbitrary fixed finite velocity observation before quotienting
the canonical radius family. -/
def generatedFiniteObservedVelocityTrajectory
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1) :
    FiniteObservedVelocityState observed :=
  fun wave =>
    generatedVelocityEndpointGalerkinWavePath
      ledger radius wave.1 time

theorem generatedFiniteObservedVelocityTrajectory_continuous
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ) :
    Continuous
      (generatedFiniteObservedVelocityTrajectory ledger observed radius) := by
  apply continuous_pi
  intro wave
  rw [continuous_iff_continuousAt]
  intro time
  let stage := ledger.family.stage radius
  have evolves := (stage.physical time.1 time.2).1
  have rowContinuous :
      ContinuousAt
        (fun actual =>
          finiteStateVelocityCoefficient
            (stage.trajectory actual) wave.1)
        time.1 :=
    (finiteStateVelocityTrajectoryWave_hasDerivAt
      stage.trajectory time.1
      (finiteStateVorticityGenerator
        (wholeRestartModes radius) nu.coeff
        (stage.trajectory time.1))
      wave.1 evolves).continuousAt
  exact rowContinuous.comp continuousAt_subtype_val

/-- Bounded-continuous realization of one actual observed Galerkin path. -/
def generatedFiniteObservedVelocityBoundedPath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) 1) (FiniteObservedVelocityState observed) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨generatedFiniteObservedVelocityTrajectory ledger observed radius,
      generatedFiniteObservedVelocityTrajectory_continuous
        ledger observed radius⟩

/-- Pointwise finite-observation norm is paid by the complete endpoint
kinetic norm, independently of the radius and observation cardinality. -/
theorem generatedFiniteObservedVelocityTrajectory_norm_le_endpoint
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1) :
    ‖generatedFiniteObservedVelocityTrajectory
        ledger observed radius time‖ ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro wave
  exact generatedVelocityEndpointGalerkinWavePath_norm_le_endpoint
    ledger radius wave.1 time

/-- Source-generated common Lipschitz ceiling for one finite observation. -/
def generatedFiniteObservedVelocitySpeedCeiling
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) : ℝ :=
  ∑ output ∈ observed,
    generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger output

theorem generatedFiniteObservedVelocitySpeedCeiling_nonneg
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) :
    0 ≤ generatedFiniteObservedVelocitySpeedCeiling ledger observed := by
  unfold generatedFiniteObservedVelocitySpeedCeiling
  exact Finset.sum_nonneg fun output outputMem =>
    generatedVelocityEndpointGalerkinWaveSpeedCeiling_nonneg ledger output

/-- The full fixed finite observation has a common radius-independent
Lipschitz modulus. -/
theorem generatedFiniteObservedVelocityTrajectory_dist_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ)
    (first second : Icc (0 : ℝ) 1) :
    dist
        (generatedFiniteObservedVelocityTrajectory
          ledger observed radius first)
        (generatedFiniteObservedVelocityTrajectory
          ledger observed radius second) ≤
      generatedFiniteObservedVelocitySpeedCeiling ledger observed *
        dist first second := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg
      (generatedFiniteObservedVelocitySpeedCeiling_nonneg ledger observed)
      dist_nonneg)).2
  intro wave
  have rowBound :=
    generatedVelocityEndpointGalerkinWavePath_dist_le_allRadius
      ledger radius wave.1 first second
  rw [dist_eq_norm] at rowBound
  exact rowBound.trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum
        (fun output outputMem =>
          generatedVelocityEndpointGalerkinWaveSpeedCeiling_nonneg
            ledger output)
        wave.2)
      dist_nonneg)

/-! ## Arzelà--Ascoli for the complete radius family -/

/-- All actual canonical-radius paths on one fixed finite observation. -/
def generatedFiniteObservedVelocityPathFamily
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) :
    Set
      (BoundedContinuousFunction
        (Icc (0 : ℝ) 1) (FiniteObservedVelocityState observed)) :=
  Set.range fun radius : ℕ =>
    generatedFiniteObservedVelocityBoundedPath ledger observed radius

theorem generatedFiniteObservedVelocityPathFamily_equicontinuous
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) :
    Equicontinuous
      (fun member :
          generatedFiniteObservedVelocityPathFamily ledger observed =>
        (member.1 : Icc (0 : ℝ) 1 →
          FiniteObservedVelocityState observed)) := by
  let ceiling := generatedFiniteObservedVelocitySpeedCeiling ledger observed
  let modulus : ℝ → ℝ := fun radius => ceiling * |radius|
  have modulusContinuous : Continuous modulus :=
    continuous_const.mul continuous_abs
  have modulusTendsToZero : Tendsto modulus (nhds 0) (nhds 0) := by
    have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
    have modulusZero : modulus 0 = 0 := by simp [modulus]
    nth_rewrite 2 [← modulusZero]
    exact atZero
  apply Metric.equicontinuous_of_continuity_modulus
    modulus modulusTendsToZero
  intro first second member
  rcases member with ⟨function, ⟨radius, functionEq⟩⟩
  subst function
  change
    dist
        (generatedFiniteObservedVelocityTrajectory
          ledger observed radius first)
        (generatedFiniteObservedVelocityTrajectory
          ledger observed radius second) ≤
      modulus (dist first second)
  simpa [modulus, ceiling, abs_of_nonneg dist_nonneg] using
    generatedFiniteObservedVelocityTrajectory_dist_le
      ledger observed radius first second

/-- The uniform closure of the complete actual radius family is compact on
every fixed finite velocity observation.  The compact set is generated in
the conclusion; no target limit or subsequence enters the mouth. -/
theorem generatedFiniteObservedVelocityPathFamily_isCompact_closure
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) :
    IsCompact
      (closure
        (generatedFiniteObservedVelocityPathFamily ledger observed)) := by
  let coefficientBall : Set (FiniteObservedVelocityState observed) :=
    Metric.closedBall 0
      ‖ledger.family.endpointReceipt.velocityEndpoint‖
  apply BoundedContinuousFunction.arzela_ascoli
    coefficientBall (isCompact_closedBall _ _)
  · intro function time functionMem
    rcases functionMem with ⟨radius, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact generatedFiniteObservedVelocityTrajectory_norm_le_endpoint
      ledger observed radius time
  · exact generatedFiniteObservedVelocityPathFamily_equicontinuous
      ledger observed

/-! ## Source-facing compactness producer -/

/-- The complete finite-observation path family generated directly from a
bounded-elapsed whole-restart source.  The uniform kinetic ledger is
constructed internally. -/
def sourceGeneratedFiniteObservedVelocityPathFamily
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (observed : Finset IntegerWavevector) :
    Set
      (BoundedContinuousFunction
        (Icc (0 : ℝ) 1) (FiniteObservedVelocityState observed)) :=
  generatedFiniteObservedVelocityPathFamily
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).toCore
    observed

/-- Source-facing Arzelà--Ascoli theorem.  Its mouth contains exactly the
actual source current, bounded elapsed-time branch, and the finite consumer
observation; the endpoint, Galerkin family, kinetic bound, time modulus,
compact set, and closure are generated in the proof. -/
theorem sourceGeneratedFiniteObservedVelocityPathFamily_isCompact_closure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (observed : Finset IntegerWavevector) :
    IsCompact
      (closure
        (sourceGeneratedFiniteObservedVelocityPathFamily
          initial elapsedBounded observed)) := by
  exact generatedFiniteObservedVelocityPathFamily_isCompact_closure
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).toCore
    observed

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
end NavierStokes
end SaturationMonoid
