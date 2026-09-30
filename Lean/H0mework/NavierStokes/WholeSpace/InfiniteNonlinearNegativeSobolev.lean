import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow
import H0mework.NavierStokes.InitialData.FiniteSupportCriticalSobolev

/-!
# Whole-carrier negative Sobolev control of the infinite nonlinearity

The fixed-output infinite convolution rows are assembled here into a genuine
full-lattice negative-one state.  For a transverse whole Fourier state with
finite vorticity-gradient mass, the module proves:

* every canonical finite nonlinear `H⁻¹` mass is bounded by one
  cutoff-independent whole-carrier expression;
* canonical row convergence transports that bound to every finite partial
  sum of the infinite nonlinear density;
* the full density is summable over `ℤ³`;
* the inverse-square-root Laplacian weighted nonlinear table is an actual
  member of `ℓ²(ℤ³; ℂ³)`;
* its squared norm is exactly the infinite nonlinear negative-one mass and
  obeys the transported global estimate.

Thus the nonlinear limit is no longer only a collection of separately
defined Fourier rows: it occupies the complete negative Sobolev forcing
carrier consumed by weak and mild Navier--Stokes formulations.  Finite
gradient mass is an analytic property of the actual state.  Summability,
cutoff exhaustion, and the weighted-carrier witness are conclusions, not
certificate fields.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev

open scoped BigOperators ENNReal Topology

open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

/-- Full vorticity-gradient mass on the actual whole Fourier carrier. -/
def wholeStateVorticityGradientMass
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑' wave : IntegerWavevector,
    integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (state wave)

/-- One Fourier density of the whole nonlinear `H⁻¹` mass. -/
def wholeStateVorticityNonlinearNegativeOneDensity
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ℝ :=
  if output = 0 then 0
  else
    ‖wholeStateVorticityNonlinearCoefficientAt state output‖ ^ 2 /
      integerWaveViscousMultiplier output

/-- Full-lattice nonlinear `H⁻¹` mass. -/
def wholeStateVorticityNonlinearNegativeOneMass
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑' output : IntegerWavevector,
    wholeStateVorticityNonlinearNegativeOneDensity state output

theorem wholeStateVorticityNonlinearNegativeOneDensity_nonneg
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    0 ≤ wholeStateVorticityNonlinearNegativeOneDensity state output := by
  unfold wholeStateVorticityNonlinearNegativeOneDensity
  split_ifs
  · rfl
  · exact div_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg output))

theorem finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes state ≤
      wholeVorticityEuclideanMass state := by
  unfold finiteStateVorticityCoefficientEnstrophy
    wholeVorticityEuclideanMass
  simpa only [vorticityRowAmplitude_sq,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
    (summable_vorticityRowAmplitude_sq state).sum_le_tsum
      modes (fun wave waveMem => sq_nonneg _)

theorem finiteStateVorticityEnstrophyMass_le_wholeGradientMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    finiteStateVorticityEnstrophyMass modes state ≤
      wholeStateVorticityGradientMass state := by
  unfold finiteStateVorticityEnstrophyMass
    wholeStateVorticityGradientMass
  exact gradientSummable.sum_le_tsum modes fun wave waveMem =>
    mul_nonneg (integerWaveNormSq_nonneg wave)
      (complexCoordinateAmplitudeSq_nonneg _)

theorem finiteStateTransverseOn_of_wholeStateTransverse
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state) :
    FiniteStateTransverseOn modes state := by
  intro wave waveMem
  exact stateTransverse wave

/-- Uniform full-carrier bound for every finite nonlinear negative-one mass. -/
theorem finiteStateVorticityNonlinearNegativeOneMass_le_whole
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    finiteStateVorticityNonlinearNegativeOneMass modes state ≤
      4 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        wholeStateVorticityGradientMass state *
        wholeVorticityEuclideanMass state := by
  have finiteNegative :=
    finiteStateVorticityNonlinearNegativeOneMass_le
      modes state
      (finiteStateTransverseOn_of_wholeStateTransverse
        modes state stateTransverse)
  have velocityBound :=
    finiteStateVelocityMajorant_sq_le_criticalGlobal
      modes state
  have gradientBound :=
    finiteStateVorticityEnstrophyMass_le_wholeGradientMass
      modes state gradientSummable
  have coefficientBound :=
    finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      modes state
  have finiteCoefficientNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes state := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have criticalConstantNonneg :
      0 ≤
        biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave) :=
    mul_nonneg biotSavartSerrinConstant_nonneg
      integerWaveCriticalKernel_tsum_nonneg
  have wholeGradientNonneg :
      0 ≤ wholeStateVorticityGradientMass state := by
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  calc
    finiteStateVorticityNonlinearNegativeOneMass modes state ≤
        4 * finiteStateVelocityMajorant modes state ^ 2 *
          finiteStateVorticityCoefficientEnstrophy modes state :=
      finiteNegative
    _ ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            finiteStateVorticityEnstrophyMass modes state) *
          finiteStateVorticityCoefficientEnstrophy modes state := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left velocityBound (by norm_num))
          finiteCoefficientNonneg
    _ ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            wholeStateVorticityGradientMass state) *
          finiteStateVorticityCoefficientEnstrophy modes state := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              gradientBound criticalConstantNonneg)
            (by norm_num))
          finiteCoefficientNonneg
    _ ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            wholeStateVorticityGradientMass state) *
          wholeVorticityEuclideanMass state := by
      exact
        mul_le_mul_of_nonneg_left coefficientBound
          (mul_nonneg (by norm_num)
            (mul_nonneg criticalConstantNonneg wholeGradientNonneg))
    _ =
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          wholeStateVorticityGradientMass state *
          wholeVorticityEuclideanMass state := by
      ring

/-- Canonical finite-row approximation to one whole nonlinear negative-one
density.  The output is not artificially truncated in the definition. -/
def canonicalCubeVorticityNonlinearNegativeOneDensity
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ℝ :=
  if output = 0 then 0
  else
    ‖finiteStateVorticityNonlinearCoefficientAt
        (integerWaveFrequencyCube radius) state output‖ ^ 2 /
      integerWaveViscousMultiplier output

theorem canonicalCubeVorticityNonlinearNegativeOneDensity_nonneg
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    0 ≤
      canonicalCubeVorticityNonlinearNegativeOneDensity
        radius state output := by
  unfold canonicalCubeVorticityNonlinearNegativeOneDensity
  split_ifs
  · rfl
  · exact div_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg output))

/-- At every fixed output, the canonical finite negative-one density
converges to the genuine infinite-row density. -/
theorem canonicalCubeVorticityNonlinearNegativeOneDensity_tendsto
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    Tendsto
      (fun radius =>
        canonicalCubeVorticityNonlinearNegativeOneDensity
          radius state output)
      atTop
      (𝓝
        (wholeStateVorticityNonlinearNegativeOneDensity
          state output)) := by
  by_cases outputZero : output = 0
  · simp [canonicalCubeVorticityNonlinearNegativeOneDensity,
      wholeStateVorticityNonlinearNegativeOneDensity, outputZero]
  · have rowTendsto :=
      finiteStateVorticityNonlinearCoefficientAt_frequencyCube_tendsto
        state stateTransverse output
    have densityTendsto :=
      (rowTendsto.norm.pow 2).div_const
        (integerWaveViscousMultiplier output)
    simpa [canonicalCubeVorticityNonlinearNegativeOneDensity,
      wholeStateVorticityNonlinearNegativeOneDensity, outputZero] using
      densityTendsto

theorem canonicalCubeVorticityNonlinearNegativeOneDensity_sum_le_mass
    (outputs : Finset IntegerWavevector)
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (outputsSubset :
      outputs ⊆ integerWaveFrequencyCube radius) :
    (∑ output ∈ outputs,
        canonicalCubeVorticityNonlinearNegativeOneDensity
          radius state output) ≤
      finiteStateVorticityNonlinearNegativeOneMass
        (integerWaveFrequencyCube radius) state := by
  unfold finiteStateVorticityNonlinearNegativeOneMass
    canonicalCubeVorticityNonlinearNegativeOneDensity
  exact
    Finset.sum_le_sum_of_subset_of_nonneg outputsSubset
      (fun output outputMem outputNotMem => by
        by_cases outputZero : output = 0
        · simp [outputZero]
        · rw [if_neg outputZero]
          exact div_nonneg (sq_nonneg _)
            (mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg output)))

/-- Every finite partial sum of the genuine infinite nonlinear `H⁻¹`
density is controlled by one cutoff-independent whole-carrier bound. -/
theorem wholeStateVorticityNonlinearNegativeOneDensity_sum_le
    (outputs : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    (∑ output ∈ outputs,
        wholeStateVorticityNonlinearNegativeOneDensity state output) ≤
      4 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        wholeStateVorticityGradientMass state *
        wholeVorticityEuclideanMass state := by
  have sumTendsto :
      Tendsto
        (fun radius =>
          ∑ output ∈ outputs,
            canonicalCubeVorticityNonlinearNegativeOneDensity
              radius state output)
        atTop
        (𝓝
          (∑ output ∈ outputs,
            wholeStateVorticityNonlinearNegativeOneDensity
              state output)) := by
    apply tendsto_finsetSum
    intro output outputMem
    exact
      canonicalCubeVorticityNonlinearNegativeOneDensity_tendsto
        state stateTransverse output
  have eventuallySubset :
      ∀ᶠ radius : ℕ in atTop,
        outputs ⊆ integerWaveFrequencyCube radius :=
    tendsto_atTop.1 integerWaveFrequencyCube_tendsto_atTop outputs
  apply le_of_tendsto sumTendsto
  filter_upwards [eventuallySubset] with radius outputsSubset
  calc
    (∑ output ∈ outputs,
        canonicalCubeVorticityNonlinearNegativeOneDensity
          radius state output) ≤
        finiteStateVorticityNonlinearNegativeOneMass
          (integerWaveFrequencyCube radius) state :=
      canonicalCubeVorticityNonlinearNegativeOneDensity_sum_le_mass
        outputs radius state outputsSubset
    _ ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          wholeStateVorticityGradientMass state *
          wholeVorticityEuclideanMass state :=
      finiteStateVorticityNonlinearNegativeOneMass_le_whole
        (integerWaveFrequencyCube radius) state
        stateTransverse gradientSummable

/-- The complete infinite nonlinear Fourier tangent is globally summable in
the homogeneous negative-one carrier whenever the actual state has finite
whole gradient mass. -/
theorem summable_wholeStateVorticityNonlinearNegativeOneDensity
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Summable fun output : IntegerWavevector =>
      wholeStateVorticityNonlinearNegativeOneDensity state output := by
  apply summable_of_sum_le
    (fun output =>
      wholeStateVorticityNonlinearNegativeOneDensity_nonneg
        state output)
  intro outputs
  exact
    wholeStateVorticityNonlinearNegativeOneDensity_sum_le
      outputs state stateTransverse gradientSummable

/-- Cutoff-free global negative-one estimate for the actual infinite
nonlinear tangent. -/
theorem wholeStateVorticityNonlinearNegativeOneMass_le
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVorticityNonlinearNegativeOneMass state ≤
      4 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        wholeStateVorticityGradientMass state *
        wholeVorticityEuclideanMass state := by
  unfold wholeStateVorticityNonlinearNegativeOneMass
  apply le_of_tendsto
    (summable_wholeStateVorticityNonlinearNegativeOneDensity
      state stateTransverse gradientSummable).hasSum
  exact Filter.Eventually.of_forall fun outputs =>
    wholeStateVorticityNonlinearNegativeOneDensity_sum_le
      outputs state stateTransverse gradientSummable

/-! ## Actual weighted `ℓ²` negative-one carrier -/

/-- The whole nonlinear row with the exact inverse square-root Laplacian
weight installed coefficientwise. -/
def wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  if output = 0 then 0
  else
    (Real.sqrt (integerWaveViscousMultiplier output))⁻¹ •
      wholeStateVorticityNonlinearCoefficientAt state output

theorem
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_norm_sq
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    ‖wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
        state output‖ ^ 2 =
      wholeStateVorticityNonlinearNegativeOneDensity state output := by
  by_cases outputZero : output = 0
  · simp [wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityNonlinearNegativeOneDensity, outputZero]
  · have multiplierPos :
        0 < integerWaveViscousMultiplier output := by
      unfold integerWaveViscousMultiplier
      exact
        mul_pos
          (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
          (integerWaveNormSq_pos outputZero)
    have multiplierNonneg :
        0 ≤ integerWaveViscousMultiplier output :=
      multiplierPos.le
    have sqrtPos :
        0 < Real.sqrt (integerWaveViscousMultiplier output) :=
      Real.sqrt_pos.2 multiplierPos
    rw [wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityNonlinearNegativeOneDensity,
      if_neg outputZero, if_neg outputZero]
    rw [norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_eq_mul_inv]
    field_simp [sqrtPos.ne']
    rw [Real.sq_sqrt multiplierNonneg]
    ring

/-- The genuine whole nonlinear tangent as an actual weighted
`ℓ²(ℤ³; ℂ³)` negative-one state.  Membership is derived from the global
summability theorem rather than supplied as a certificate. -/
def wholeStateVorticityNonlinearNegativeOneState
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 :=
  ⟨wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (summable_wholeStateVorticityNonlinearNegativeOneDensity
        state stateTransverse gradientSummable).congr
          (fun output =>
            (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_norm_sq
              state output).symm)⟩

@[simp] theorem wholeStateVorticityNonlinearNegativeOneState_apply
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable output =
      wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
        state output :=
  rfl

theorem wholeStateVorticityNonlinearNegativeOneState_norm_sq
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    ‖wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable‖ ^ 2 =
      wholeStateVorticityNonlinearNegativeOneMass state := by
  rw [show
    ‖wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable‖ ^ 2 =
      ∑' output : IntegerWavevector,
        ‖wholeStateVorticityNonlinearNegativeOneState
          state stateTransverse gradientSummable output‖ ^ 2 by
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (wholeStateVorticityNonlinearNegativeOneState
            state stateTransverse gradientSummable))]
  unfold wholeStateVorticityNonlinearNegativeOneMass
  apply tsum_congr
  intro output
  rw [wholeStateVorticityNonlinearNegativeOneState_apply,
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_norm_sq]

/-- Norm bound in the actual weighted negative-one carrier. -/
theorem wholeStateVorticityNonlinearNegativeOneState_norm_sq_le
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    ‖wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable‖ ^ 2 ≤
      4 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        wholeStateVorticityGradientMass state *
        wholeVorticityEuclideanMass state := by
  rw [wholeStateVorticityNonlinearNegativeOneState_norm_sq]
  exact
    wholeStateVorticityNonlinearNegativeOneMass_le
      state stateTransverse gradientSummable

end

end ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
end NavierStokes
end SaturationMonoid
