import H0mework.Versions.X.NavierStokes.Butterfly.PhysicalMaterial
import H0mework.NavierStokes.Accumulation.FiniteSupportWholeActionTube
import H0mework.NavierStokes.Fourier.WholeTransverseNonlinearDerivative

/-!
# Actual next-butterfly pair material

The first physical butterfly receipt generates an axis receiver and retains
the alternating pump. This module treats their two ordered NS interactions as
one continuous bilinear material, proves its exact source derivative, and
generates a nonzero actual-time persistence window.

The result is a same-receipt pair occurrence. It does not identify that pair
with the complete whole nonlinear row; the complementary full fibre remains
visible as the next commuting obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open scoped Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube

noncomputable section

def complexRowPairContribution
    (first second : IntegerWavevector)
    (firstRow secondRow : ComplexCoordinateVector) :
    ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector second ⬝ᵥ firstRow)) •
        biotSavartVelocityCoefficient second secondRow -
    (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector second ⬝ᵥ
        biotSavartVelocityCoefficient first firstRow)) •
          secondRow

private theorem biotSavartVelocityCoefficient_add_row
    (wave : IntegerWavevector)
    (left right : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient wave (left + right) =
      biotSavartVelocityCoefficient wave left +
        biotSavartVelocityCoefficient wave right := by
  by_cases waveZero : wave = 0
  · subst wave
    simp
  · rw [biotSavartVelocityCoefficient, if_neg waveZero,
      biotSavartVelocityCoefficient, if_neg waveZero,
      biotSavartVelocityCoefficient, if_neg waveZero]
    funext coordinate
    fin_cases coordinate <;>
      simp [cross_apply] <;>
      ring

private theorem biotSavartVelocityCoefficient_real_smul
    (wave : IntegerWavevector)
    (scalar : ℝ)
    (row : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient wave (scalar • row) =
      scalar • biotSavartVelocityCoefficient wave row := by
  have inputEq : scalar • row = (scalar : ℂ) • row := by
    funext coordinate
    simp [Pi.smul_apply, Complex.real_smul]
  have outputEq :
      scalar • biotSavartVelocityCoefficient wave row =
        (scalar : ℂ) • biotSavartVelocityCoefficient wave row := by
    funext coordinate
    simp [Pi.smul_apply, Complex.real_smul]
  rw [inputEq, biotSavartVelocityCoefficient_smul, outputEq]

def complexRowPairContributionLinear
    (first second : IntegerWavevector) :
    ComplexCoordinateVector →ₗ[ℝ]
      ComplexCoordinateVector →ₗ[ℝ] ComplexCoordinateVector :=
  LinearMap.mk₂ ℝ (complexRowPairContribution first second)
    (by
      intros
      simp [complexRowPairContribution, dotProduct_add,
        biotSavartVelocityCoefficient_add_row]
      module)
    (by
      intros
      simp [complexRowPairContribution, dotProduct_smul,
        biotSavartVelocityCoefficient_real_smul]
      module)
    (by
      intros
      simp [complexRowPairContribution,
        biotSavartVelocityCoefficient_add_row, smul_add]
      module)
    (by
      intros
      simp [complexRowPairContribution,
        biotSavartVelocityCoefficient_real_smul]
      module)

noncomputable def complexRowPairContributionRightCLM
    (first second : IntegerWavevector)
    (left : ComplexCoordinateVector) :
    ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector := by
  let linear := complexRowPairContributionLinear first second left
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

noncomputable def complexRowPairContributionCLM
    (first second : IntegerWavevector) :
    ComplexCoordinateVector →L[ℝ]
      ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector := by
  let linear : ComplexCoordinateVector →ₗ[ℝ]
      ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector :=
    { toFun := complexRowPairContributionRightCLM first second
      map_add' := by
        intro left right
        ext value coordinate
        simp [complexRowPairContributionRightCLM,
          complexRowPairContributionLinear]
      map_smul' := by
        intro scalar left
        ext value coordinate
        simp [complexRowPairContributionRightCLM,
          complexRowPairContributionLinear] }
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

theorem complexRowPairContribution_hasDerivAt
    (first second : IntegerWavevector)
    (left right : ℝ → ComplexCoordinateVector)
    (time : ℝ)
    (left' right' : ComplexCoordinateVector)
    (leftDeriv : HasDerivAt left left' time)
    (rightDeriv : HasDerivAt right right' time) :
    HasDerivAt
      (fun actual => complexRowPairContribution first second
        (left actual) (right actual))
      (complexRowPairContribution first second left' (right time) +
        complexRowPairContribution first second (left time) right')
      time := by
  have generated :=
    (complexRowPairContributionCLM first second).hasDerivAt_of_bilinear
      (fun _ => leftDeriv) (fun _ => rightDeriv)
  simpa [complexRowPairContributionCLM,
    complexRowPairContributionRightCLM,
    complexRowPairContributionLinear, add_comm] using generated

def butterflyAxisPath (nu : Viscosity) :
    ℝ → ComplexCoordinateVector :=
  actualWholeContinuousHeatDuhamelPath
    (butterflyReceipt nu) (axisWave 4)

def butterflyPumpPath (nu : Viscosity) :
    ℝ → ComplexCoordinateVector :=
  actualWholeContinuousHeatDuhamelPath
    (butterflyReceipt nu) pumpY

def butterflyNextSidebandPairPath (nu : Viscosity) :
    ℝ → ComplexCoordinateVector :=
  (fun actual => complexRowPairContribution (axisWave 4) pumpY
      (butterflyAxisPath nu actual) (butterflyPumpPath nu actual)) +
    fun actual => complexRowPairContribution pumpY (axisWave 4)
      (butterflyPumpPath nu actual) (butterflyAxisPath nu actual)

theorem butterflyAxisPath_zero (nu : Viscosity) :
    butterflyAxisPath nu 0 = 0 := by
  unfold butterflyAxisPath actualWholeContinuousHeatDuhamelPath
    ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport.heatDuhamelComplexCoordinatePath
    ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport.intervalIntegralComplexCoordinatePath
  simp [butterflyPhysicalSeed_wholeState,
    butterflyPhysicalState_target_zero]

theorem butterflyPumpPath_zero (nu : Viscosity) :
    butterflyPumpPath nu 0 = butterflyPhysicalState 1 pumpY := by
  exact butterflyReceipt_pumpY_zero nu

theorem butterflyPhysicalState_pumpY_eq :
    butterflyPhysicalState 1 pumpY =
      GaussianRatVector.toComplex (realRow 1 0 1) := by
  rw [butterflyPhysicalState_apply, if_pos (by decide)]
  simp [butterflySeedRow, pumpY]

theorem butterflyNextSidebandDerivativeRow_eq :
    complexRowPairContribution (axisWave 4) pumpY
          (GaussianRatVector.toComplex (butterflySeedFullFibre 1))
          (butterflyPhysicalState 1 pumpY) +
        complexRowPairContribution pumpY (axisWave 4)
          (butterflyPhysicalState 1 pumpY)
          (GaussianRatVector.toComplex (butterflySeedFullFibre 1)) =
      GaussianRatVector.toComplex (sidebandPlusY 4 (-24 / 5)) := by
  rw [butterflyPhysicalState_pumpY_eq,
    butterflySeedFullFibre_eq, butterflyZTwoFullFibre_eq,
    sidebandPlusY_eq 4 (by norm_num)]
  funext coordinate
  fin_cases coordinate <;>
    simp [complexRowPairContribution,
      biotSavartVelocityCoefficient, axisWave, pumpY,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, complexWavevector, integerWaveNormSq,
      dotProduct, cross_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Pi.smul_apply, smul_eq_mul] <;>
    field_simp [Real.pi_ne_zero]
  all_goals simp [Complex.I_sq]
  all_goals ring

theorem butterflyNextSidebandPairPath_hasDerivAt_zero
    (nu : Viscosity) :
    HasDerivAt (butterflyNextSidebandPairPath nu)
      (GaussianRatVector.toComplex (sidebandPlusY 4 (-24 / 5))) 0 := by
  let pumpDerivative :=
    wholeStateVorticityNonlinearCoefficientAt
          (wholeRestartPhysicalState (butterflyPhysicalSeed nu)) pumpY -
      (nu.coeff * integerWaveViscousMultiplier pumpY) •
        wholeRestartPhysicalState (butterflyPhysicalSeed nu) pumpY
  have axisDeriv := butterflyReceipt_target_hasDerivAt_zero nu
  have pumpDeriv : HasDerivAt (butterflyPumpPath nu)
      pumpDerivative 0 := by
    exact actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      (butterflyReceipt nu) pumpY
  have first := complexRowPairContribution_hasDerivAt
    (axisWave 4) pumpY (butterflyAxisPath nu) (butterflyPumpPath nu)
      0 (GaussianRatVector.toComplex (butterflySeedFullFibre 1))
      pumpDerivative axisDeriv pumpDeriv
  have second := complexRowPairContribution_hasDerivAt
    pumpY (axisWave 4) (butterflyPumpPath nu) (butterflyAxisPath nu)
      0 pumpDerivative
      (GaussianRatVector.toComplex (butterflySeedFullFibre 1))
      pumpDeriv axisDeriv
  have combined := first.add second
  have derivativeEq :
      (complexRowPairContribution (axisWave 4) pumpY
            (GaussianRatVector.toComplex (butterflySeedFullFibre 1))
            (butterflyPumpPath nu 0) +
          complexRowPairContribution (axisWave 4) pumpY
            (butterflyAxisPath nu 0) pumpDerivative) +
        (complexRowPairContribution pumpY (axisWave 4)
            pumpDerivative (butterflyAxisPath nu 0) +
          complexRowPairContribution pumpY (axisWave 4)
            (butterflyPumpPath nu 0)
            (GaussianRatVector.toComplex (butterflySeedFullFibre 1))) =
        GaussianRatVector.toComplex (sidebandPlusY 4 (-24 / 5)) := by
    rw [butterflyAxisPath_zero, butterflyPumpPath_zero]
    simpa [complexRowPairContribution] using
      butterflyNextSidebandDerivativeRow_eq
  have adjusted := combined.congr_deriv derivativeEq
  change HasDerivAt
    ((fun actual => complexRowPairContribution (axisWave 4) pumpY
        (butterflyAxisPath nu actual) (butterflyPumpPath nu actual)) +
      fun actual => complexRowPairContribution pumpY (axisWave 4)
        (butterflyPumpPath nu actual) (butterflyAxisPath nu actual))
    (GaussianRatVector.toComplex (sidebandPlusY 4 (-24 / 5))) 0
  exact adjusted

theorem butterflyNextSidebandDerivative_ne_zero :
    GaussianRatVector.toComplex (sidebandPlusY 4 (-24 / 5)) ≠ 0 := by
  rw [sidebandPlusY_eq 4 (by norm_num)]
  intro rowZero
  have secondZero := congrFun rowZero 1
  norm_num [realRow, realGaussian, GaussianRatVector.toComplex,
    GaussianRat.toComplex, Matrix.cons_val_one] at secondZero

theorem exists_butterflyNextSidebandPairPersistenceTime
    (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        butterflyNextSidebandPairPath nu actual ≠ 0 := by
  have punctured :=
    (butterflyNextSidebandPairPath_hasDerivAt_zero nu).eventually_ne
      butterflyNextSidebandDerivative_ne_zero
      (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in nhds (0 : Real), actual ≠ 0 →
        butterflyNextSidebandPairPath nu actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

noncomputable def butterflyNextSidebandPairPersistenceTime
    (nu : Viscosity) : Real :=
  Classical.choose (exists_butterflyNextSidebandPairPersistenceTime nu)

theorem butterflyNextSidebandPairPersistenceTime_pos
    (nu : Viscosity) :
    0 < butterflyNextSidebandPairPersistenceTime nu :=
  (Classical.choose_spec
    (exists_butterflyNextSidebandPairPersistenceTime nu)).1

theorem butterflyNextSidebandPairPersistenceTime_spec
    (nu : Viscosity) (actual : Real)
    (actualPos : 0 < actual)
    (actualLt : actual < butterflyNextSidebandPairPersistenceTime nu) :
    butterflyNextSidebandPairPath nu actual ≠ 0 :=
  (Classical.choose_spec
    (exists_butterflyNextSidebandPairPersistenceTime nu)).2
      actual actualPos actualLt

def butterflyNextSidebandTarget : IntegerWavevector :=
  axisWave 4 + pumpY

theorem butterflySeedRationalNextSideband_zero :
    rationalVorticityNonlinearCoefficientAt
        butterflySeedModes (butterflySeedRow 1)
        butterflyNextSidebandTarget = 0 := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [rationalVorticityNonlinearCoefficientAt,
      rationalVorticityBilinearCoefficientAt,
      butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
      butterflyZTwoRow, butterflyNextSidebandTarget,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      axisWave, pumpY, pumpZ, realRow, realGaussian,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

theorem butterflyPhysicalState_wholeNonlinear_nextSideband_zero :
    wholeStateVorticityNonlinearCoefficientAt
        (butterflyPhysicalState 1) butterflyNextSidebandTarget = 0 := by
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1) butterflyNextSidebandTarget]
  have bridge := rationalVorticityNonlinearCoefficientAt_toComplex
    butterflySeedModes (butterflySeedRow 1) (butterflyPhysicalState 1)
      butterflyNextSidebandTarget butterflySeedModes_zero_not_mem
      (fun wave waveMem =>
        (butterflyPhysicalState_apply 1 wave).trans
          (if_pos waveMem) |>.symm)
  rw [butterflySeedRationalNextSideband_zero,
    GaussianRatVector.toComplex_zero_instance] at bridge
  exact bridge.symm

def butterflyNextSidebandFullRowPath (nu : Viscosity) :
    ℝ → ComplexCoordinateVector :=
  actualWholeContinuousNonlinearRow
    (butterflyReceipt nu) butterflyNextSidebandTarget

def butterflyNextSidebandComplementPath (nu : Viscosity) :
    ℝ → ComplexCoordinateVector :=
  butterflyNextSidebandFullRowPath nu -
    butterflyNextSidebandPairPath nu

theorem butterflyNextSidebandFullRowPath_zero (nu : Viscosity) :
    butterflyNextSidebandFullRowPath nu 0 = 0 := by
  unfold butterflyNextSidebandFullRowPath
  rw [actualWholeContinuousNonlinearRow_zero]
  exact butterflyPhysicalState_wholeNonlinear_nextSideband_zero

theorem butterflyNextSidebandPairPath_zero (nu : Viscosity) :
    butterflyNextSidebandPairPath nu 0 = 0 := by
  unfold butterflyNextSidebandPairPath
  change
    complexRowPairContribution (axisWave 4) pumpY
          (butterflyAxisPath nu 0) (butterflyPumpPath nu 0) +
        complexRowPairContribution pumpY (axisWave 4)
          (butterflyPumpPath nu 0) (butterflyAxisPath nu 0) = 0
  rw [butterflyAxisPath_zero]
  simp [complexRowPairContribution]

theorem butterflyNextSidebandComplementPath_zero (nu : Viscosity) :
    butterflyNextSidebandComplementPath nu 0 = 0 := by
  simp [butterflyNextSidebandComplementPath,
    butterflyNextSidebandFullRowPath_zero,
    butterflyNextSidebandPairPath_zero]

/-- The exact next-row obstruction: the full actual nonlinear row inherits
the nonzero butterfly derivative exactly when the complementary whole fibre
is little-o of time at the source occurrence. -/
theorem butterflyNextSidebandFullRow_hasDerivAt_iff_complement
    (nu : Viscosity) :
    HasDerivAt (butterflyNextSidebandFullRowPath nu)
        (GaussianRatVector.toComplex (sidebandPlusY 4 (-24 / 5))) 0 ↔
      HasDerivAt (butterflyNextSidebandComplementPath nu) 0 0 := by
  constructor
  · intro fullDeriv
    have difference := fullDeriv.sub
      (butterflyNextSidebandPairPath_hasDerivAt_zero nu)
    simpa [butterflyNextSidebandComplementPath] using difference
  · intro complementDeriv
    have restored := complementDeriv.add
      (butterflyNextSidebandPairPath_hasDerivAt_zero nu)
    simpa [butterflyNextSidebandComplementPath] using restored

/-! ## Complete source linearization -/

/-- Exact rational table of the same finite physical seed. -/
def butterflyRationalSeedState : GaussianRatState := fun wave =>
  if wave ∈ butterflySeedModes then butterflySeedRow 1 wave else 0

/-- The punctured action inventory generated by the seed. -/
def butterflyRationalActionModes : Finset IntegerWavevector :=
  (wholeFiniteSupportActionModes butterflySeedModes).erase 0

theorem butterflySeedModes_subset_rationalActionModes :
    butterflySeedModes ⊆ butterflyRationalActionModes := by
  intro wave waveMem
  rw [butterflyRationalActionModes, Finset.mem_erase]
  exact ⟨fun waveZero =>
      butterflySeedModes_zero_not_mem (waveZero ▸ waveMem),
    modes_subset_wholeFiniteSupportActionModes
      butterflySeedModes waveMem⟩

/-- Source-generated first whole action in exact rational coordinates. -/
def butterflyRationalTangentState : GaussianRatState :=
  rationalVorticityGeneratorCoefficientAt
    butterflySeedModes 1 butterflyRationalSeedState

/-- Complete linearization of the next-sideband nonlinear row. -/
def butterflyRationalFullNextSidebandDerivative : GaussianRatVector :=
  rationalVorticityBilinearCoefficientAt butterflyRationalActionModes
      butterflyRationalTangentState butterflyRationalSeedState
      butterflyNextSidebandTarget +
    rationalVorticityBilinearCoefficientAt butterflyRationalActionModes
      butterflyRationalSeedState butterflyRationalTangentState
      butterflyNextSidebandTarget

def butterflyRationalFullNextSidebandDerivativeAt
    (sourceWave : IntegerWavevector) : GaussianRatVector :=
  rationalVorticityPairContribution
      (butterflyNextSidebandTarget - sourceWave) sourceWave
      (butterflyRationalTangentState
        (butterflyNextSidebandTarget - sourceWave))
      (butterflySeedRow 1 sourceWave) +
    rationalVorticityPairContribution sourceWave
      (butterflyNextSidebandTarget - sourceWave)
      (butterflySeedRow 1 sourceWave)
      (butterflyRationalTangentState
        (butterflyNextSidebandTarget - sourceWave))

def butterflyRationalFullNextSidebandDerivativeReduced :
    GaussianRatVector :=
  ∑ sourceWave ∈ butterflySeedModes,
    if butterflyNextSidebandTarget - sourceWave ∈
        butterflyRationalActionModes then
      butterflyRationalFullNextSidebandDerivativeAt sourceWave
    else 0

/-- Only four actual seed incidences can reach the selected output through
the first generated action inventory. -/
def butterflyRationalDerivativeSourceModes :
    Finset IntegerWavevector :=
  {axisWave 2, axisWave 2 + pumpZ, axisWave 2 - pumpZ, pumpY}

theorem butterflyRationalDerivativeSourceModes_eq_filter :
    butterflySeedModes.filter (fun sourceWave =>
      butterflyNextSidebandTarget - sourceWave ∈
        butterflyRationalActionModes) =
      butterflyRationalDerivativeSourceModes := by
  decide

theorem butterflyRationalFullNextSidebandDerivativeReduced_eq_activeSum :
    butterflyRationalFullNextSidebandDerivativeReduced =
      ∑ sourceWave ∈ butterflyRationalDerivativeSourceModes,
        butterflyRationalFullNextSidebandDerivativeAt sourceWave := by
  unfold butterflyRationalFullNextSidebandDerivativeReduced
  rw [← Finset.sum_filter]
  rw [butterflyRationalDerivativeSourceModes_eq_filter]

/-- The full double convolution is definitionally the same four-incidence
material after the finite-support slot is consumed. -/
theorem butterflyRationalFullNextSidebandDerivative_eq_reduced :
    butterflyRationalFullNextSidebandDerivative =
      butterflyRationalFullNextSidebandDerivativeReduced := by
  rw [butterflyRationalFullNextSidebandDerivative,
    rationalVorticityBilinearCoefficientAt_eq_source_right
      butterflySeedModes butterflyRationalActionModes
      butterflySeedModes_subset_rationalActionModes
      butterflyRationalTangentState butterflyRationalSeedState
      (by
        intro wave waveNotMem
        simp [butterflyRationalSeedState, waveNotMem])
      butterflyNextSidebandTarget,
    rationalVorticityBilinearCoefficientAt_eq_source_left
      butterflySeedModes butterflyRationalActionModes
      butterflySeedModes_subset_rationalActionModes
      butterflyRationalSeedState butterflyRationalTangentState
      (by
        intro wave waveNotMem
        simp [butterflyRationalSeedState, waveNotMem])
      butterflyNextSidebandTarget]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sourceWave sourceMem
  by_cases counterpartMem :
      butterflyNextSidebandTarget - sourceWave ∈
        butterflyRationalActionModes
  · have sourceRow :
        butterflyRationalSeedState sourceWave =
          butterflySeedRow 1 sourceWave := by
        simp [butterflyRationalSeedState, sourceMem]
    simp only [if_pos counterpartMem]
    rw [sourceRow]
    rfl
  · simp [counterpartMem]

/-- Exact complete first variation.  The complementary fibre is retained;
its nonzero contribution is part of this row rather than discarded. -/
theorem butterflyRationalFullNextSidebandDerivative_eq :
    butterflyRationalFullNextSidebandDerivative =
      ![⟨8 / 15, 0⟩, ⟨-32 / 15, 0⟩, ⟨-5063 / 150, 0⟩] := by
  rw [butterflyRationalFullNextSidebandDerivative_eq_reduced,
    butterflyRationalFullNextSidebandDerivativeReduced_eq_activeSum]
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp (config := { maxSteps := 1000000 })
      [butterflyRationalFullNextSidebandDerivativeAt,
      butterflyRationalTangentState,
      rationalVorticityGeneratorCoefficientAt,
      rationalVorticityNonlinearCoefficientAt,
      rationalVorticityBilinearCoefficientAt,
      butterflyRationalDerivativeSourceModes,
      butterflyRationalSeedState,
      butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
      butterflyZTwoRow, butterflyNextSidebandTarget,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      axisWave, pumpY, pumpZ, realRow, realGaussian,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      GaussianRatVector.add, GaussianRatVector.sub,
      GaussianRatVector.ratScale, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    norm_num

theorem butterflyRationalFullNextSidebandDerivative_ne_zero :
    butterflyRationalFullNextSidebandDerivative ≠ 0 := by
  rw [butterflyRationalFullNextSidebandDerivative_eq]
  intro rowZero
  have firstZero := congrFun rowZero 0
  have realZero := congrArg GaussianRat.re firstZero
  norm_num [Matrix.cons_val_zero] at realZero

/-- The old zero-complement gate is false at the exact source
linearization: the retained complement is explicit and nonzero. -/
theorem butterflyRationalNextSidebandComplementDerivative_eq :
    GaussianRatVector.sub
        butterflyRationalFullNextSidebandDerivative
        (sidebandPlusY 4 (-24 / 5)) =
      ![⟨-2 / 3, 0⟩, ⟨8 / 3, 0⟩, ⟨-2363 / 150, 0⟩] := by
  rw [butterflyRationalFullNextSidebandDerivative_eq,
    sidebandPlusY_eq 4 (by norm_num)]
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [GaussianRatVector.sub, realRow, realGaussian,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      GaussianRat.sub, GaussianRat.add, GaussianRat.neg] <;>
    norm_num

theorem butterflyRationalNextSidebandComplementDerivative_ne_zero :
    GaussianRatVector.sub
        butterflyRationalFullNextSidebandDerivative
        (sidebandPlusY 4 (-24 / 5)) ≠ 0 := by
  rw [butterflyRationalNextSidebandComplementDerivative_eq]
  intro rowZero
  have firstZero := congrFun rowZero 0
  have realZero := congrArg GaussianRat.re firstZero
  norm_num [Matrix.cons_val_zero] at realZero

/-! ## Physical whole-action commuting -/

/-- Viscosity whose Fourier-scaled coefficient is the rational unit used by
the exact evaluator. -/
def butterflyViscosity : Viscosity where
  coeff := 1 / (2 * Real.pi) ^ 2
  coeff_pos := by positivity

theorem butterflyViscosity_scaled :
    butterflyViscosity.coeff * (2 * Real.pi) ^ 2 =
      ((1 : ℚ) : ℝ) := by
  unfold butterflyViscosity
  field_simp [Real.pi_ne_zero]
  norm_num

def butterflyPhysicalActionState : ComplexVorticityHilbertState :=
  wholeFiniteSupportActionState butterflyViscosity.coeff
    butterflySeedModes (butterflyPhysicalState 1)

theorem butterflyRationalSeedState_toComplex
    (wave : IntegerWavevector) :
    GaussianRatVector.toComplex (butterflyRationalSeedState wave) =
      butterflyPhysicalState 1 wave := by
  by_cases waveMem : wave ∈ butterflySeedModes
  · simp [butterflyRationalSeedState,
      butterflyPhysicalState_apply, waveMem]
  · simp [butterflyRationalSeedState,
      butterflyPhysicalState_apply, waveMem]

theorem butterflyRationalTangentState_toComplex
    (wave : IntegerWavevector) :
    GaussianRatVector.toComplex (butterflyRationalTangentState wave) =
      butterflyPhysicalActionState wave := by
  have bridge := rationalVorticityGeneratorCoefficientAt_toComplex
    butterflySeedModes 1 butterflyRationalSeedState
    (butterflyPhysicalState 1) wave butterflyViscosity.coeff
    butterflySeedModes_zero_not_mem
    (fun actual _actualMem =>
      butterflyRationalSeedState_toComplex actual)
    (butterflyRationalSeedState_toComplex wave)
    butterflyViscosity_scaled
  rw [butterflyPhysicalActionState,
    wholeFiniteSupportActionState_apply_eq_wholeTangent
      butterflyViscosity.coeff butterflySeedModes
      (butterflyPhysicalState 1)
      (butterflyPhysicalState_supported 1) wave]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1) wave]
  exact bridge

theorem butterflyRationalActionModes_zero_not_mem :
    (0 : IntegerWavevector) ∉ butterflyRationalActionModes := by
  simp [butterflyRationalActionModes]

theorem butterflyPhysicalActionState_supported
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ butterflyRationalActionModes) :
    butterflyPhysicalActionState wave = 0 := by
  unfold butterflyPhysicalActionState
  by_cases waveZero : wave = 0
  · subst wave
    rw [wholeFiniteSupportActionState_apply_eq_wholeTangent
      butterflyViscosity.coeff butterflySeedModes
      (butterflyPhysicalState 1)
      (butterflyPhysicalState_supported 1) 0]
    exact wholeLatticeVorticityFourierTangentAt_zero
      butterflyViscosity.coeff (butterflyPhysicalState 1)
      (butterflyPhysicalState_transverse 1)
      (butterflyPhysicalState_zero 1)
  · apply wholeFiniteSupportActionState_supported
    exact fun waveMem => waveNotMem (Finset.mem_erase.mpr ⟨waveZero, waveMem⟩)

theorem butterflyPhysicalState_supported_on_action
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ butterflyRationalActionModes) :
    butterflyPhysicalState 1 wave = 0 := by
  apply butterflyPhysicalState_supported 1 wave
  intro waveMem
  exact waveNotMem (butterflySeedModes_subset_rationalActionModes waveMem)

/-- The exact rational full variation is the physical complete whole
bilinear variation of the same source/action occurrence. -/
theorem butterflyRationalFullNextSidebandDerivative_toComplex :
    GaussianRatVector.toComplex
        butterflyRationalFullNextSidebandDerivative =
      wholeStateVorticityBilinearCoefficientAt
          butterflyPhysicalActionState (butterflyPhysicalState 1)
          butterflyNextSidebandTarget +
        wholeStateVorticityBilinearCoefficientAt
          (butterflyPhysicalState 1) butterflyPhysicalActionState
          butterflyNextSidebandTarget := by
  have rightBridge := rationalVorticityBilinearCoefficientAt_toComplex
    butterflyRationalActionModes
    butterflyRationalTangentState butterflyRationalSeedState
    butterflyPhysicalActionState (butterflyPhysicalState 1)
    butterflyNextSidebandTarget
    butterflyRationalActionModes_zero_not_mem
    (fun wave _waveMem => butterflyRationalTangentState_toComplex wave)
    (fun wave _waveMem => butterflyRationalSeedState_toComplex wave)
  have leftBridge := rationalVorticityBilinearCoefficientAt_toComplex
    butterflyRationalActionModes
    butterflyRationalSeedState butterflyRationalTangentState
    (butterflyPhysicalState 1) butterflyPhysicalActionState
    butterflyNextSidebandTarget
    butterflyRationalActionModes_zero_not_mem
    (fun wave _waveMem => butterflyRationalSeedState_toComplex wave)
    (fun wave _waveMem => butterflyRationalTangentState_toComplex wave)
  rw [butterflyRationalFullNextSidebandDerivative]
  rw [GaussianRatVector.toComplex_add_instance]
  change
    GaussianRatVector.toComplex
          (rationalVorticityBilinearCoefficientAt
            butterflyRationalActionModes butterflyRationalTangentState
            butterflyRationalSeedState butterflyNextSidebandTarget) +
        GaussianRatVector.toComplex
          (rationalVorticityBilinearCoefficientAt
            butterflyRationalActionModes butterflyRationalSeedState
            butterflyRationalTangentState butterflyNextSidebandTarget) = _
  rw [rightBridge, leftBridge]
  rw [wholeStateVorticityBilinearCoefficientAt_eq_finite_of_supported
      butterflyRationalActionModes butterflyPhysicalActionState
      (butterflyPhysicalState 1)
      butterflyPhysicalActionState_supported
      butterflyPhysicalState_supported_on_action
      butterflyNextSidebandTarget,
    wholeStateVorticityBilinearCoefficientAt_eq_finite_of_supported
      butterflyRationalActionModes (butterflyPhysicalState 1)
      butterflyPhysicalActionState
      butterflyPhysicalState_supported_on_action
      butterflyPhysicalActionState_supported
      butterflyNextSidebandTarget]

def butterflyPhysicalFullNextSidebandDerivative :
    ComplexCoordinateVector :=
  GaussianRatVector.toComplex
    butterflyRationalFullNextSidebandDerivative

theorem butterflyPhysicalFullNextSidebandDerivative_eq :
    butterflyPhysicalFullNextSidebandDerivative =
      GaussianRatVector.toComplex
        ![⟨8 / 15, 0⟩, ⟨-32 / 15, 0⟩, ⟨-5063 / 150, 0⟩] := by
  rw [butterflyPhysicalFullNextSidebandDerivative,
    butterflyRationalFullNextSidebandDerivative_eq]

theorem butterflyPhysicalFullNextSidebandDerivative_ne_zero :
    butterflyPhysicalFullNextSidebandDerivative ≠ 0 := by
  unfold butterflyPhysicalFullNextSidebandDerivative
  rw [butterflyRationalFullNextSidebandDerivative_eq]
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [GaussianRatVector.toComplex, GaussianRat.toComplex,
    Matrix.cons_val_zero] at firstZero

def butterflyWholeTransversePath :
    ℝ → ↥ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow.wholeTransverseVorticitySubmodule :=
  fun actual =>
    ⟨(actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) actual).1,
      (actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) actual).2⟩

/-- Once the actual whole transverse path exposes its physical right
derivative,
the complete nonlinear row reads the explicit full material above. -/
theorem butterflyNextSidebandFullRowPath_hasDerivWithinAt_zero_of_wholePath
    (pathDerivative :
      HasDerivWithinAt
        butterflyWholeTransversePath
        ⟨butterflyPhysicalActionState,
          wholeFiniteSupportActionState_transverse
            butterflyViscosity.coeff butterflySeedModes
            (butterflyPhysicalState 1)
            (butterflyPhysicalState_supported 1)
            (butterflyPhysicalState_transverse 1)⟩
        (Set.Ici 0) 0) :
    HasDerivWithinAt
      (butterflyNextSidebandFullRowPath butterflyViscosity)
      butterflyPhysicalFullNextSidebandDerivative (Set.Ici 0) 0 := by
  have generated :=
    ThreeDimensionalVorticityCoefficientWholeTransverseNonlinearDerivative.wholeTransverseNonlinear_hasDerivWithinAt
      butterflyNextSidebandTarget
      butterflyWholeTransversePath
      ⟨butterflyPhysicalActionState,
        wholeFiniteSupportActionState_transverse
          butterflyViscosity.coeff butterflySeedModes
          (butterflyPhysicalState 1)
          (butterflyPhysicalState_supported 1)
          (butterflyPhysicalState_transverse 1)⟩
      0 (Set.Ici 0) pathDerivative
  have sourceAtZero :
      (actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) 0).1 =
        butterflyPhysicalState 1 := by
    change
      (butterflyReceipt butterflyViscosity).wholePath
          (Set.projIcc (0 : ℝ)
            (wholeRestartDuration
              (butterflyPhysicalSeed butterflyViscosity))
            (butterflyReceipt butterflyViscosity).requestedTimePos.le 0) =
        butterflyPhysicalState 1
    rw [Set.projIcc_of_mem
      (butterflyReceipt butterflyViscosity).requestedTimePos.le
      ⟨le_rfl,
        (butterflyReceipt butterflyViscosity).requestedTimePos.le⟩]
    exact (butterflyReceipt butterflyViscosity).wholePath_initial
  have sourceAtZero' :
      (butterflyWholeTransversePath 0).1 =
        butterflyPhysicalState 1 := by
    exact sourceAtZero
  change HasDerivWithinAt
    (fun actual =>
      wholeStateVorticityNonlinearCoefficientAt
        (actualWholeProjectedTransversePath
          (butterflyReceipt butterflyViscosity) actual).1
        butterflyNextSidebandTarget)
    butterflyPhysicalFullNextSidebandDerivative (Set.Ici 0) 0
  rw [sourceAtZero'] at generated
  rw [butterflyPhysicalFullNextSidebandDerivative,
    butterflyRationalFullNextSidebandDerivative_toComplex]
  simpa [butterflyWholeTransversePath,
    butterflyNextSidebandFullRowPath,
    actualWholeContinuousNonlinearRow, add_comm] using generated


end
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
