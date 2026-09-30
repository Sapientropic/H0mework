import H0mework.NavierStokes.Accumulation.ConcreteSource
import H0mework.NavierStokes.Accumulation.NativeRestartCellIncidence
import H0mework.NavierStokes.InitialData.RawSourceInitialCriticalLoad

/-!
# Concrete source-generated cell regeneration seed

A phase-reversed, amplitude-scaled concrete Fourier source generates an exact
first quantized-cell crossing.  The same actual receipt exposes the finite
net-enstrophy debit and its regeneration seam on the fixed native successor.
No future recurrence, contact-time summability, endpoint state, branch, or
target certificate is accepted from a caller.
-/

set_option autoImplicit false

open scoped BigOperators Interval

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteCellRegeneration

open MeasureTheory

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientConcreteActivePair
open ThreeDimensionalVorticityCoefficientConcreteActiveClosedTriad
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientRawSourceInitialCriticalLoad
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteThreeDimensionalSource
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteEffectRecurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRestartCellIncidence
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart

noncomputable section

/-- A fixed lift lower bound only implies a fixed whole-mass lower bound.  It
does not by itself reach the moving wall `level n - 1`. -/
theorem concreteInitial_lift_supplies_fixed_mass_floor :
    (1 / 8 : Real) <
      restartPhysicalVorticityMass concreteCounterexampleInitial 0 := by
  simpa only [restartPhysicalVorticityMass, run_zero,
    concreteCounterexampleInitial] using
    concreteThreeDimensionalActiveLiftCurrent_contact_wholeMass_gt
      concreteCounterexampleViscosity

private theorem concreteThreeDimensional_generatedVorticity_neg_transported :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        ![0, -1, 0] =
      ![0, 0, (1 / 2 : Complex)] := by
  have waveEq : (![0, -1, 0] : IntegerWavevector) =
      waveNeg concreteTransportedWave := by decide
  rw [waveEq]
  rw [generatedVorticityCoefficient_waveNeg,
    concreteThreeDimensional_generatedVorticity_transported]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteThreeDimensional_generatedVorticity_neg_testing :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        ![1, 1, 0] =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  have waveEq : (![1, 1, 0] : IntegerWavevector) =
      waveNeg concreteTestingWave := by decide
  rw [waveEq]
  rw [generatedVorticityCoefficient_waveNeg,
    concreteThreeDimensional_generatedVorticity_testing]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteThreeDimensional_generatedVorticity_neg_advecting :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        ![-1, 0, 0] =
      ![0, (1 / 2 : Complex), 0] := by
  have waveEq : (![-1, 0, 0] : IntegerWavevector) =
      waveNeg concreteAdvectingWave := by decide
  rw [waveEq]
  rw [generatedVorticityCoefficient_waveNeg,
    concreteThreeDimensional_generatedVorticity_advecting]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteThreeDimensional_advecting_fiber_eq :
    generatedStretchingPairFiber concreteThreeDimensionalSource
        concreteAdvectingWave =
      {(waveNeg concreteTransportedWave,
          waveNeg concreteTestingWave),
        (waveNeg concreteTestingWave,
          waveNeg concreteTransportedWave)} := by
  decide

set_option maxHeartbeats 800000 in
theorem concreteThreeDimensional_nonlinear_advecting :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteAdvectingWave =
      ![0, (1 / 4 : Complex), 0] := by
  rw [generatedVorticityNonlinearCoefficientAt,
    concreteThreeDimensional_advecting_fiber_eq]
  have pairNotMem :
      (waveNeg concreteTransportedWave,
          waveNeg concreteTestingWave) ∉
        ({(waveNeg concreteTestingWave,
          waveNeg concreteTransportedWave)} : Finset StretchingPair) := by
    decide
  rw [Finset.sum_insert pairNotMem, Finset.sum_singleton]
  unfold generatedVorticityNonlinearPairContribution
    generatedStretchingPairContribution
    generatedVorticityAdvectionPairContribution
    generatedVelocityCoefficient
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient, concreteTransportedWave,
      concreteTestingWave, waveNeg, complexWavevector,
      integerWaveNormSq, cross_apply, dotProduct, Fin.sum_univ_succ,
      concreteThreeDimensional_generatedVorticity_neg_transported,
      concreteThreeDimensional_generatedVorticity_neg_testing]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

private theorem concreteThreeDimensional_transported_fiber_eq :
    generatedStretchingPairFiber concreteThreeDimensionalSource
        concreteTransportedWave =
      {(waveNeg concreteAdvectingWave,
          waveNeg concreteTestingWave),
        (waveNeg concreteTestingWave,
          waveNeg concreteAdvectingWave)} := by
  decide

set_option maxHeartbeats 800000 in
theorem concreteThreeDimensional_nonlinear_transported :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteTransportedWave = 0 := by
  rw [generatedVorticityNonlinearCoefficientAt,
    concreteThreeDimensional_transported_fiber_eq]
  have pairNotMem :
      (waveNeg concreteAdvectingWave,
          waveNeg concreteTestingWave) ∉
        ({(waveNeg concreteTestingWave,
          waveNeg concreteAdvectingWave)} : Finset StretchingPair) := by
    decide
  rw [Finset.sum_insert pairNotMem, Finset.sum_singleton]
  unfold generatedVorticityNonlinearPairContribution
    generatedStretchingPairContribution
    generatedVorticityAdvectionPairContribution
    generatedVelocityCoefficient
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient, concreteAdvectingWave,
      concreteTestingWave, waveNeg, complexWavevector,
      integerWaveNormSq, cross_apply, dotProduct, Fin.sum_univ_succ,
      concreteThreeDimensional_generatedVorticity_neg_advecting,
      concreteThreeDimensional_generatedVorticity_neg_testing]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf

theorem concreteThreeDimensional_nonlinear_testing :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteTestingWave =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  have reality :=
    generatedVorticityNonlinearCoefficientAt_waveNeg
      concreteThreeDimensionalSource concreteTestingWave
  have conjugated := congrArg vectorConj reality
  rw [vectorConj_involutive] at conjugated
  rw [← concreteStretchingOutput_eq_waveNeg_testing,
    concreteThreeDimensional_nonlinearOutput] at conjugated
  have vectorConjEq :
      vectorConj (![(-1 / 4 : Complex), (1 / 4 : Complex), 0]) =
        ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
    funext coordinate
    fin_cases coordinate <;> norm_num [vectorConj]
  rw [vectorConjEq] at conjugated
  exact conjugated.symm

private theorem concreteThreeDimensional_lift_fiber_eq_empty :
    generatedStretchingPairFiber concreteThreeDimensionalSource
        concreteLiftWave = ∅ := by
  decide

theorem concreteThreeDimensional_nonlinear_lift :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteLiftWave = 0 := by
  rw [generatedVorticityNonlinearCoefficientAt,
    concreteThreeDimensional_lift_fiber_eq_empty]
  simp

private theorem concreteVorticity_lift_pos_explicit :
    generatedVorticityCoefficient concreteThreeDimensionalSource ![0, 0, 1] =
      ![(1 / 2 : Complex), 0, 0] := by
  simpa only [concreteLiftWave] using
    concreteThreeDimensional_generatedVorticity_lift

private theorem concreteVorticity_lift_neg_explicit :
    generatedVorticityCoefficient concreteThreeDimensionalSource ![0, 0, -1] =
      ![(1 / 2 : Complex), 0, 0] := by
  have waveEq : (![0, 0, -1] : IntegerWavevector) =
      waveNeg concreteLiftWave := by decide
  rw [waveEq, generatedVorticityCoefficient_waveNeg,
    concreteThreeDimensional_generatedVorticity_lift]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteVorticity_advecting_pos_explicit :
    generatedVorticityCoefficient concreteThreeDimensionalSource ![1, 0, 0] =
      ![0, (1 / 2 : Complex), 0] := by
  simpa only [concreteAdvectingWave] using
    concreteThreeDimensional_generatedVorticity_advecting

private theorem concreteVorticity_transported_pos_explicit :
    generatedVorticityCoefficient concreteThreeDimensionalSource ![0, 1, 0] =
      ![0, 0, (1 / 2 : Complex)] := by
  simpa only [concreteTransportedWave] using
    concreteThreeDimensional_generatedVorticity_transported

private theorem concreteVorticity_testing_pos_explicit :
    generatedVorticityCoefficient concreteThreeDimensionalSource ![-1, -1, 0] =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  simpa only [concreteTestingWave] using
    concreteThreeDimensional_generatedVorticity_testing

private theorem concreteNonlinear_lift_pos_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![0, 0, 1] = 0 := by
  simpa only [concreteLiftWave] using
    concreteThreeDimensional_nonlinear_lift

private theorem concreteNonlinear_lift_neg_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![0, 0, -1] = 0 := by
  have waveEq : (![0, 0, -1] : IntegerWavevector) =
      waveNeg concreteLiftWave := by decide
  rw [waveEq, generatedVorticityNonlinearCoefficientAt_waveNeg,
    concreteThreeDimensional_nonlinear_lift, vectorConj_zero]

private theorem concreteNonlinear_advecting_pos_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![1, 0, 0] =
      ![0, (1 / 4 : Complex), 0] := by
  simpa only [concreteAdvectingWave] using
    concreteThreeDimensional_nonlinear_advecting

private theorem concreteNonlinear_advecting_neg_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![-1, 0, 0] =
      ![0, (1 / 4 : Complex), 0] := by
  have waveEq : (![-1, 0, 0] : IntegerWavevector) =
      waveNeg concreteAdvectingWave := by decide
  rw [waveEq, generatedVorticityNonlinearCoefficientAt_waveNeg,
    concreteThreeDimensional_nonlinear_advecting]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteNonlinear_transported_pos_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![0, 1, 0] = 0 := by
  simpa only [concreteTransportedWave] using
    concreteThreeDimensional_nonlinear_transported

private theorem concreteNonlinear_transported_neg_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![0, -1, 0] = 0 := by
  have waveEq : (![0, -1, 0] : IntegerWavevector) =
      waveNeg concreteTransportedWave := by decide
  rw [waveEq, generatedVorticityNonlinearCoefficientAt_waveNeg,
    concreteThreeDimensional_nonlinear_transported, vectorConj_zero]

private theorem concreteNonlinear_testing_pos_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![-1, -1, 0] =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  simpa only [concreteTestingWave] using
    concreteThreeDimensional_nonlinear_testing

private theorem concreteNonlinear_testing_neg_explicit :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource ![1, 1, 0] =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  have waveEq : (![1, 1, 0] : IntegerWavevector) =
      waveNeg concreteTestingWave := by decide
  rw [waveEq, generatedVorticityNonlinearCoefficientAt_waveNeg,
    concreteThreeDimensional_nonlinear_testing]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteThreeDimensional_generatedSupport_explicit :
    generatedSupport concreteThreeDimensionalSource =
      {concreteLiftWave, waveNeg concreteLiftWave,
        concreteAdvectingWave, waveNeg concreteAdvectingWave,
        concreteTransportedWave, waveNeg concreteTransportedWave,
        concreteTestingWave, waveNeg concreteTestingWave} := by
  decide

theorem concreteThreeDimensionalState_wholeMass_eq_five_halves :
    wholeVorticityEuclideanMass concreteThreeDimensionalState =
      (5 / 2 : Real) := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    (generatedSupport concreteThreeDimensionalSource)
    concreteThreeDimensionalState]
  · unfold finiteStateVorticityCoefficientEnstrophy
    rw [concreteThreeDimensional_generatedSupport_explicit]
    norm_num [concreteThreeDimensionalState,
      generatedComplexVorticityState_apply,
      concreteThreeDimensional_generatedSupport_explicit,
      generatedVorticityCoefficient_waveNeg,
      concreteThreeDimensional_generatedVorticity_lift,
      concreteThreeDimensional_generatedVorticity_advecting,
      concreteThreeDimensional_generatedVorticity_transported,
      concreteThreeDimensional_generatedVorticity_testing,
      concreteVorticity_lift_pos_explicit,
      concreteVorticity_lift_neg_explicit,
      concreteVorticity_advecting_pos_explicit,
      concreteThreeDimensional_generatedVorticity_neg_advecting,
      concreteVorticity_transported_pos_explicit,
      concreteThreeDimensional_generatedVorticity_neg_transported,
      concreteVorticity_testing_pos_explicit,
      concreteThreeDimensional_generatedVorticity_neg_testing,
      concreteLiftWave, concreteAdvectingWave, concreteTransportedWave,
      concreteTestingWave, waveNeg, vectorConj,
      complexCoordinateAmplitudeSq, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · intro wave waveNotMem
    simp [concreteThreeDimensionalState,
      generatedComplexVorticityState_apply, waveNotMem]

theorem concreteThreeDimensionalSeed_level_eq_four
    (nu : Viscosity) :
    wholeRestartCoefficientLevel (concreteThreeDimensionalSeed nu) = 4 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  change Nat.ceil
    (wholeVorticityEuclideanMass concreteThreeDimensionalState + 1) = 4
  rw [concreteThreeDimensionalState_wholeMass_eq_five_halves]
  norm_num

theorem concreteThreeDimensionalSeed_cellGap_eq_half
    (nu : Viscosity) :
    (wholeRestartCoefficientLevel (concreteThreeDimensionalSeed nu) : Real) -
        1 - wholeVorticityEuclideanMass concreteThreeDimensionalState =
      1 / 2 := by
  rw [concreteThreeDimensionalSeed_level_eq_four,
    concreteThreeDimensionalState_wholeMass_eq_five_halves]
  norm_num

set_option maxHeartbeats 800000 in
theorem concreteThreeDimensionalState_fullNonlinearWork_eq_neg_quarter :
    finiteStateVorticityNonlinearWork
        (generatedSupport concreteThreeDimensionalSource)
        concreteThreeDimensionalState = (-1 / 4 : Real) := by
  classical
  unfold concreteThreeDimensionalState
  unfold finiteStateVorticityNonlinearWork
  simp_rw [finiteStateVorticityNonlinearCoefficientAt_generatedSource]
  rw [concreteThreeDimensional_generatedSupport_explicit]
  norm_num [generatedComplexVorticityState_apply,
    generatedVorticityCoefficient_waveNeg,
    generatedVorticityNonlinearCoefficientAt_waveNeg,
    concreteThreeDimensional_generatedVorticity_lift,
    concreteThreeDimensional_generatedVorticity_advecting,
    concreteThreeDimensional_generatedVorticity_transported,
    concreteThreeDimensional_generatedVorticity_testing,
    concreteThreeDimensional_nonlinear_lift,
    concreteThreeDimensional_nonlinear_advecting,
    concreteThreeDimensional_nonlinear_transported,
    concreteThreeDimensional_nonlinear_testing,
    concreteVorticity_lift_pos_explicit,
    concreteVorticity_lift_neg_explicit,
    concreteVorticity_advecting_pos_explicit,
    concreteThreeDimensional_generatedVorticity_neg_advecting,
    concreteVorticity_transported_pos_explicit,
    concreteThreeDimensional_generatedVorticity_neg_transported,
    concreteVorticity_testing_pos_explicit,
    concreteThreeDimensional_generatedVorticity_neg_testing,
    concreteNonlinear_lift_pos_explicit,
    concreteNonlinear_lift_neg_explicit,
    concreteNonlinear_advecting_pos_explicit,
    concreteNonlinear_advecting_neg_explicit,
    concreteNonlinear_transported_pos_explicit,
    concreteNonlinear_transported_neg_explicit,
    concreteNonlinear_testing_pos_explicit,
    concreteNonlinear_testing_neg_explicit,
    concreteLiftWave, concreteAdvectingWave, concreteTransportedWave,
    concreteTestingWave, waveNeg, vectorConj,
    complexCoordinateRealInner, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- At the raw concrete state the complete Galerkin half-enstrophy tangent
is strictly negative for every positive viscosity.  Thus the currently
installed fixed-mode/lift facts do not themselves furnish the signed cell
gain required by a recursive `+1` invariant. -/
theorem concreteThreeDimensionalState_generator_realWork_neg
    (nu : Viscosity) :
    (∑ wave ∈ generatedSupport concreteThreeDimensionalSource,
      complexCoordinateRealInner (concreteThreeDimensionalState wave)
        (finiteStateVorticityGenerator
          (generatedSupport concreteThreeDimensionalSource) nu.coeff
          concreteThreeDimensionalState wave)) < 0 := by
  rw [finiteStateVorticityGenerator_realWork,
    concreteThreeDimensionalState_fullNonlinearWork_eq_neg_quarter]
  have viscousCostNonneg :
      0 ≤ nu.coeff * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass
          (generatedSupport concreteThreeDimensionalSource)
          concreteThreeDimensionalState := by
    exact mul_nonneg
      (mul_nonneg nu.coeff_pos.le (sq_nonneg _))
      (finiteStateVorticityEnstrophyMass_nonneg _ _)
  linarith

/-! ## Exact sign/scale source-selection probe -/

/-- Full one-parameter source family retaining the exact Fourier geometry.
The amplitude/phase scale is source data; no future cell or action result is
stored in it. -/
def concreteScaledThreeDimensionalSource
    (scale : Real) : RawVorticityFourierSource :=
  realScaleRawVorticitySource scale concreteThreeDimensionalSource

def concreteScaledThreeDimensionalState
    (scale : Real) : ComplexVorticityHilbertState :=
  generatedComplexVorticityState
    (concreteScaledThreeDimensionalSource scale)
    (generatedSupport (concreteScaledThreeDimensionalSource scale))

theorem concreteScaledThreeDimensionalState_eq_smul
    (scale : Real) :
    concreteScaledThreeDimensionalState scale =
      scale • concreteThreeDimensionalState := by
  unfold concreteScaledThreeDimensionalState
    concreteScaledThreeDimensionalSource concreteThreeDimensionalState
  rw [realScaleRawVorticitySource_generatedSupport,
    generatedComplexVorticityState_realScale]
  exact (RCLike.real_smul_eq_coe_smul (K := Complex) scale
    (generatedComplexVorticityState concreteThreeDimensionalSource
      (generatedSupport concreteThreeDimensionalSource))).symm

theorem concreteScaledThreeDimensionalState_wholeMass
    (scale : Real) :
    wholeVorticityEuclideanMass
        (concreteScaledThreeDimensionalState scale) =
      scale ^ 2 * (5 / 2 : Real) := by
  rw [concreteScaledThreeDimensionalState_eq_smul,
    wholeVorticityEuclideanMass_real_smul,
    concreteThreeDimensionalState_wholeMass_eq_five_halves]

theorem concreteScaledThreeDimensionalState_supported
    (scale : Real)
    (wave : IntegerWavevector)
    (waveNotMem :
      wave ∉ generatedSupport (concreteScaledThreeDimensionalSource scale)) :
    concreteScaledThreeDimensionalState scale wave = 0 := by
  have baseNotMem :
      wave ∉ generatedSupport concreteThreeDimensionalSource := by
    simpa [concreteScaledThreeDimensionalSource] using waveNotMem
  rw [concreteScaledThreeDimensionalState_eq_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  have baseZero : concreteThreeDimensionalState wave = 0 := by
    simp [concreteThreeDimensionalState,
      generatedComplexVorticityState_apply, baseNotMem]
  rw [baseZero, smul_zero]

/-- Reversing phase and doubling amplitude keeps the physical support while
placing the raw mass exactly on an integer cell wall. -/
def concreteGrowingThreeDimensionalSource : RawVorticityFourierSource :=
  concreteScaledThreeDimensionalSource (-2)

def concreteGrowingThreeDimensionalState : ComplexVorticityHilbertState :=
  concreteScaledThreeDimensionalState (-2)

theorem concreteGrowingThreeDimensionalState_eq_neg_two_smul :
    concreteGrowingThreeDimensionalState =
      (-2 : Real) • concreteThreeDimensionalState := by
  exact concreteScaledThreeDimensionalState_eq_smul (-2)

theorem concreteGrowingThreeDimensionalState_wholeMass_eq_ten :
    wholeVorticityEuclideanMass concreteGrowingThreeDimensionalState = 10 := by
  rw [concreteGrowingThreeDimensionalState_eq_neg_two_smul,
    wholeVorticityEuclideanMass_real_smul,
    concreteThreeDimensionalState_wholeMass_eq_five_halves]
  norm_num

private theorem complexCoordinateRealInner_real_smul_left
    (scale : Real)
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scale • left) right =
      scale * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp
  ring

private theorem complexCoordinateRealInner_real_smul_cubic
    (scale : Real)
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scale • left)
        (((scale : Complex) ^ 2) • right) =
      scale ^ 3 * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  simp only [Pi.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := Complex), smul_eq_mul, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  norm_num
  ring

theorem concreteScaledThreeDimensionalState_fullNonlinearWork_eq_cube_mul
    (scale : Real) :
    finiteStateVorticityNonlinearWork
        (generatedSupport (concreteScaledThreeDimensionalSource scale))
        (concreteScaledThreeDimensionalState scale) =
      scale ^ 3 *
        finiteStateVorticityNonlinearWork
          (generatedSupport concreteThreeDimensionalSource)
          concreteThreeDimensionalState := by
  let modes := generatedSupport concreteThreeDimensionalSource
  have baseSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → concreteThreeDimensionalState wave = 0 := by
    intro wave waveNotMem
    simp [modes, concreteThreeDimensionalState,
      generatedComplexVorticityState_apply, waveNotMem]
  have scaledSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → concreteScaledThreeDimensionalState scale wave = 0 := by
    intro wave waveNotMem
    rw [concreteScaledThreeDimensionalState_eq_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply,
      baseSupported wave waveNotMem, smul_zero]
  rw [show generatedSupport (concreteScaledThreeDimensionalSource scale) =
    modes by rfl]
  unfold finiteStateVorticityNonlinearWork
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [← wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    modes (concreteScaledThreeDimensionalState scale) scaledSupported wave]
  rw [concreteScaledThreeDimensionalState_eq_smul,
    wholeStateVorticityNonlinearCoefficientAt_real_smul]
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    modes concreteThreeDimensionalState baseSupported wave]
  exact complexCoordinateRealInner_real_smul_cubic scale _ _

theorem concreteGrowingThreeDimensionalState_fullNonlinearWork_eq_cube_mul :
    finiteStateVorticityNonlinearWork
        (generatedSupport concreteGrowingThreeDimensionalSource)
        concreteGrowingThreeDimensionalState =
      (-2 : Real) ^ 3 *
        finiteStateVorticityNonlinearWork
          (generatedSupport concreteThreeDimensionalSource)
          concreteThreeDimensionalState :=
  concreteScaledThreeDimensionalState_fullNonlinearWork_eq_cube_mul (-2)

/-- The same finite physical source with phase/amplitude `-2` has exact
positive complete nonlinear enstrophy work `2`. -/
theorem concreteGrowingThreeDimensionalState_fullNonlinearWork_eq_two :
    finiteStateVorticityNonlinearWork
        (generatedSupport concreteGrowingThreeDimensionalSource)
        concreteGrowingThreeDimensionalState = 2 := by
  rw [concreteGrowingThreeDimensionalState_fullNonlinearWork_eq_cube_mul,
    concreteThreeDimensionalState_fullNonlinearWork_eq_neg_quarter]
  norm_num

theorem concreteThreeDimensionalState_enstrophyMass_eq_seven_halves :
    finiteStateVorticityEnstrophyMass
        (generatedSupport concreteThreeDimensionalSource)
        concreteThreeDimensionalState = (7 / 2 : Real) := by
  classical
  unfold finiteStateVorticityEnstrophyMass
  rw [concreteThreeDimensional_generatedSupport_explicit]
  norm_num [concreteThreeDimensionalState,
    generatedComplexVorticityState_apply,
    concreteThreeDimensional_generatedSupport_explicit,
    generatedVorticityCoefficient_waveNeg,
    concreteThreeDimensional_generatedVorticity_lift,
    concreteThreeDimensional_generatedVorticity_advecting,
    concreteThreeDimensional_generatedVorticity_transported,
    concreteThreeDimensional_generatedVorticity_testing,
    concreteVorticity_lift_pos_explicit,
    concreteVorticity_lift_neg_explicit,
    concreteVorticity_advecting_pos_explicit,
    concreteThreeDimensional_generatedVorticity_neg_advecting,
    concreteVorticity_transported_pos_explicit,
    concreteThreeDimensional_generatedVorticity_neg_transported,
    concreteVorticity_testing_pos_explicit,
    concreteThreeDimensional_generatedVorticity_neg_testing,
    concreteLiftWave, concreteAdvectingWave, concreteTransportedWave,
    concreteTestingWave, waveNeg, integerWaveNormSq,
    complexCoordinateAmplitudeSq, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private theorem complexCoordinateAmplitudeSq_real_smul
    (scale : Real)
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (scale • vector) =
      scale ^ 2 * complexCoordinateAmplitudeSq vector := by
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  change complexCoordinateVectorNormSq ((scale : Complex) • vector) = _
  rw [complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
  ring

theorem concreteScaledThreeDimensionalState_enstrophyMass
    (scale : Real) :
    finiteStateVorticityEnstrophyMass
        (generatedSupport (concreteScaledThreeDimensionalSource scale))
        (concreteScaledThreeDimensionalState scale) =
      scale ^ 2 * (7 / 2 : Real) := by
  rw [show generatedSupport (concreteScaledThreeDimensionalSource scale) =
    generatedSupport concreteThreeDimensionalSource by rfl,
    concreteScaledThreeDimensionalState_eq_smul]
  unfold finiteStateVorticityEnstrophyMass
  simp_rw [lp.coeFn_smul, Pi.smul_apply,
    complexCoordinateAmplitudeSq_real_smul]
  calc
    (∑ wave ∈ generatedSupport concreteThreeDimensionalSource,
        integerWaveNormSq wave *
          (scale ^ 2 *
            complexCoordinateAmplitudeSq
              (concreteThreeDimensionalState wave))) =
        scale ^ 2 *
          finiteStateVorticityEnstrophyMass
            (generatedSupport concreteThreeDimensionalSource)
            concreteThreeDimensionalState := by
      unfold finiteStateVorticityEnstrophyMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _
      ring
    _ = scale ^ 2 * (7 / 2 : Real) := by
      rw [concreteThreeDimensionalState_enstrophyMass_eq_seven_halves]

theorem concreteGrowingThreeDimensionalState_enstrophyMass_eq_fourteen :
    finiteStateVorticityEnstrophyMass
        (generatedSupport concreteGrowingThreeDimensionalSource)
        concreteGrowingThreeDimensionalState = 14 := by
  change
    finiteStateVorticityEnstrophyMass
        (generatedSupport (concreteScaledThreeDimensionalSource (-2)))
        (concreteScaledThreeDimensionalState (-2)) = 14
  rw [concreteScaledThreeDimensionalState_enstrophyMass]
  norm_num

/-- Exact source polynomial for the complete half-enstrophy tangent of the
scaled family.  This retains amplitude, viscosity and Fourier geometry in one
source relation; sign and quantitative margins are downstream readouts. -/
theorem concreteScaledThreeDimensionalState_generator_realWork
    (scale : Real)
    (nu : Viscosity) :
    (∑ wave ∈ generatedSupport
          (concreteScaledThreeDimensionalSource scale),
      complexCoordinateRealInner
        (concreteScaledThreeDimensionalState scale wave)
        (finiteStateVorticityGenerator
          (generatedSupport (concreteScaledThreeDimensionalSource scale))
          nu.coeff
          (concreteScaledThreeDimensionalState scale) wave)) =
      scale ^ 3 * (-1 / 4 : Real) -
        nu.coeff * (2 * Real.pi) ^ 2 *
          (scale ^ 2 * (7 / 2 : Real)) := by
  rw [finiteStateVorticityGenerator_realWork,
    concreteScaledThreeDimensionalState_fullNonlinearWork_eq_cube_mul,
    concreteThreeDimensionalState_fullNonlinearWork_eq_neg_quarter,
    concreteScaledThreeDimensionalState_enstrophyMass]

/-- Viscosity-dependent phase/amplitude selected from the exact source
polynomial. -/
def concreteRegeneratingScale (nu : Viscosity) : Real :=
  -112 * Real.pi ^ 2 * nu.coeff

def concreteRegeneratingThreeDimensionalSource
    (nu : Viscosity) : RawVorticityFourierSource :=
  concreteScaledThreeDimensionalSource (concreteRegeneratingScale nu)

def concreteRegeneratingThreeDimensionalState
    (nu : Viscosity) : ComplexVorticityHilbertState :=
  concreteScaledThreeDimensionalState (concreteRegeneratingScale nu)

/-- The source-selected scaling makes the complete half-enstrophy tangent an
explicit positive product for every viscosity. -/
theorem concreteRegeneratingThreeDimensionalState_generator_realWork
    (nu : Viscosity) :
    (∑ wave ∈ generatedSupport
          (concreteRegeneratingThreeDimensionalSource nu),
      complexCoordinateRealInner
        (concreteRegeneratingThreeDimensionalState nu wave)
        (finiteStateVorticityGenerator
          (generatedSupport (concreteRegeneratingThreeDimensionalSource nu))
          nu.coeff
          (concreteRegeneratingThreeDimensionalState nu) wave)) =
      (112 * Real.pi ^ 2 * nu.coeff) ^ 2 *
        (14 * Real.pi ^ 2 * nu.coeff) := by
  change
    (∑ wave ∈ generatedSupport
          (concreteScaledThreeDimensionalSource
            (concreteRegeneratingScale nu)),
      complexCoordinateRealInner
        (concreteScaledThreeDimensionalState
          (concreteRegeneratingScale nu) wave)
        (finiteStateVorticityGenerator
          (generatedSupport (concreteScaledThreeDimensionalSource
            (concreteRegeneratingScale nu)))
          nu.coeff
          (concreteScaledThreeDimensionalState
            (concreteRegeneratingScale nu)) wave)) = _
  rw [concreteScaledThreeDimensionalState_generator_realWork]
  unfold concreteRegeneratingScale
  ring

theorem concreteRegeneratingThreeDimensionalState_generator_realWork_pos
    (nu : Viscosity) :
    0 <
      ∑ wave ∈ generatedSupport
          (concreteRegeneratingThreeDimensionalSource nu),
        complexCoordinateRealInner
          (concreteRegeneratingThreeDimensionalState nu wave)
          (finiteStateVorticityGenerator
            (generatedSupport (concreteRegeneratingThreeDimensionalSource nu))
            nu.coeff
            (concreteRegeneratingThreeDimensionalState nu) wave) := by
  rw [concreteRegeneratingThreeDimensionalState_generator_realWork]
  exact mul_pos
    (sq_pos_of_pos (mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      nu.coeff_pos))
    (mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      nu.coeff_pos)

theorem concreteRegeneratingThreeDimensionalState_zero
    (nu : Viscosity) :
    concreteRegeneratingThreeDimensionalState nu 0 = 0 := by
  unfold concreteRegeneratingThreeDimensionalState
  rw [concreteScaledThreeDimensionalState_eq_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply,
    concreteThreeDimensionalState_zero, smul_zero]

theorem concreteRegeneratingThreeDimensionalState_transverse
    (nu : Viscosity) :
    WholeStateTransverse (concreteRegeneratingThreeDimensionalState nu) := by
  unfold concreteRegeneratingThreeDimensionalState
  rw [concreteScaledThreeDimensionalState_eq_smul]
  exact wholeStateTransverse_real_smul _ _
    concreteThreeDimensionalState_transverse

theorem concreteRegeneratingThreeDimensionalState_reality
    (nu : Viscosity) :
    FiniteStateFourierReality
      (concreteRegeneratingThreeDimensionalState nu) := by
  intro wave
  unfold concreteRegeneratingThreeDimensionalState
  rw [concreteScaledThreeDimensionalState_eq_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [concreteThreeDimensionalState_reality]
  funext coordinate
  simp [vectorConj]

/-- Premise-free viscosity-indexed physical seed generated from the exact
source polynomial. -/
def concreteRegeneratingThreeDimensionalSeed
    (nu : Viscosity) : SourceOwnedWholeRestartPhysicalSeed nu where
  physicalState := concreteRegeneratingThreeDimensionalState nu
  physicalState_zero := concreteRegeneratingThreeDimensionalState_zero nu
  transverse := concreteRegeneratingThreeDimensionalState_transverse nu
  reality := concreteRegeneratingThreeDimensionalState_reality nu

def concreteRegeneratingThreeDimensionalReplay (nu : Viscosity) :=
  generatedWholeRestartCanonicalReplay
    (concreteRegeneratingThreeDimensionalSeed nu)

def concreteRegeneratingThreeDimensionalReceipt (nu : Viscosity) :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    (concreteRegeneratingThreeDimensionalReplay nu)

def concreteRegeneratingThreeDimensionalContact (nu : Viscosity) :=
  generatedPositiveWholeRestartContact
    (concreteRegeneratingThreeDimensionalReceipt nu)

/-- Actual viscosity-dependent current.  Its receipt, contact and complete
cell effect are all emitted from the same source seed. -/
def concreteRegeneratingThreeDimensionalCurrent
    (nu : Viscosity) : GeneratedWholeRestartCurrent nu where
  initialState := concreteRegeneratingThreeDimensionalState nu
  duration := wholeRestartDuration
    (concreteRegeneratingThreeDimensionalSeed nu)
  receipt := concreteRegeneratingThreeDimensionalReceipt nu
  contact := concreteRegeneratingThreeDimensionalContact nu

/-- The exact positive source tangent is already the time-zero net-power row
of the generated whole receipt. -/
theorem concreteRegeneratingThreeDimensionalReceipt_netPower_zero
    (nu : Viscosity) :
    actualProjectedWholeNetEnstrophyPower
        (concreteRegeneratingThreeDimensionalReceipt nu)
        (generatedSupport (concreteRegeneratingThreeDimensionalSource nu)) 0 =
      2 * ((112 * Real.pi ^ 2 * nu.coeff) ^ 2 *
        (14 * Real.pi ^ 2 * nu.coeff)) := by
  have sourceReadout :=
    actualProjectedWholeNetEnstrophyPower_zero_eq_generatorRealWork
      (concreteRegeneratingThreeDimensionalReceipt nu)
      (generatedSupport (concreteRegeneratingThreeDimensionalSource nu))
      (fun wave waveNotMem => by
        exact concreteScaledThreeDimensionalState_supported
          (concreteRegeneratingScale nu) wave waveNotMem)
  rw [sourceReadout]
  rw [show wholeRestartPhysicalState
      (concreteRegeneratingThreeDimensionalSeed nu) =
        concreteRegeneratingThreeDimensionalState nu by rfl]
  rw [concreteRegeneratingThreeDimensionalState_generator_realWork]

theorem concreteRegeneratingThreeDimensionalReceipt_netPower_zero_pos
    (nu : Viscosity) :
    0 < actualProjectedWholeNetEnstrophyPower
        (concreteRegeneratingThreeDimensionalReceipt nu)
        (generatedSupport (concreteRegeneratingThreeDimensionalSource nu)) 0 := by
  rw [concreteRegeneratingThreeDimensionalReceipt_netPower_zero]
  have firstPos : 0 < 112 * Real.pi ^ 2 * nu.coeff :=
    mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      nu.coeff_pos
  have secondPos : 0 < 14 * Real.pi ^ 2 * nu.coeff :=
    mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      nu.coeff_pos
  exact mul_pos (by norm_num) (mul_pos (sq_pos_of_pos firstPos) secondPos)

/-- Regeneration-aligned candidate at the already source-selected final
viscosity.  It is kept distinct from the legacy outflux candidate until the
whole-run settlement invariant chooses the final public initial. -/
def concreteRegeneratingCounterexampleInitial :
    GeneratedWholeRestartCurrent concreteCounterexampleViscosity :=
  concreteRegeneratingThreeDimensionalCurrent
    concreteCounterexampleViscosity

theorem concreteRegeneratingCounterexampleInitial_netPower_zero_pos :
    0 < actualProjectedWholeNetEnstrophyPower
        (concreteRegeneratingThreeDimensionalReceipt
          concreteCounterexampleViscosity)
        (generatedSupport (concreteRegeneratingThreeDimensionalSource
          concreteCounterexampleViscosity)) 0 :=
  concreteRegeneratingThreeDimensionalReceipt_netPower_zero_pos
    concreteCounterexampleViscosity

/-- The viscosity is selected from the exact generated gradient mass, so the
initial complete half-enstrophy tangent is exactly one. -/
def concreteGrowingViscosity : Viscosity where
  coeff := 1 / ((2 * Real.pi) ^ 2 * 14)
  coeff_pos := by
    exact one_div_pos.mpr
      (mul_pos (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
        (by norm_num))

theorem concreteRegeneratingScale_concreteGrowingViscosity_eq_neg_two :
    concreteRegeneratingScale concreteGrowingViscosity = -2 := by
  unfold concreteRegeneratingScale concreteGrowingViscosity
  field_simp [Real.pi_ne_zero]
  ring

theorem concreteRegeneratingState_concreteGrowingViscosity_eq :
    concreteRegeneratingThreeDimensionalState concreteGrowingViscosity =
      concreteGrowingThreeDimensionalState := by
  unfold concreteRegeneratingThreeDimensionalState
    concreteGrowingThreeDimensionalState
  rw [concreteRegeneratingScale_concreteGrowingViscosity_eq_neg_two]

theorem concreteGrowingThreeDimensionalState_generator_realWork_eq_one :
    (∑ wave ∈ generatedSupport concreteGrowingThreeDimensionalSource,
      complexCoordinateRealInner (concreteGrowingThreeDimensionalState wave)
        (finiteStateVorticityGenerator
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingViscosity.coeff
          concreteGrowingThreeDimensionalState wave)) = 1 := by
  change
    (∑ wave ∈ generatedSupport
          (concreteScaledThreeDimensionalSource (-2)),
      complexCoordinateRealInner
        (concreteScaledThreeDimensionalState (-2) wave)
        (finiteStateVorticityGenerator
          (generatedSupport (concreteScaledThreeDimensionalSource (-2)))
          concreteGrowingViscosity.coeff
          (concreteScaledThreeDimensionalState (-2)) wave)) = 1
  rw [concreteScaledThreeDimensionalState_generator_realWork]
  change
    (-2 : Real) ^ 3 * (-1 / 4) -
      (1 / ((2 * Real.pi) ^ 2 * 14)) *
        (2 * Real.pi) ^ 2 * ((-2 : Real) ^ 2 * (7 / 2)) = 1
  field_simp [Real.pi_ne_zero]
  norm_num

theorem concreteGrowingThreeDimensionalState_zero :
    concreteGrowingThreeDimensionalState 0 = 0 := by
  rw [concreteGrowingThreeDimensionalState_eq_neg_two_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply,
    concreteThreeDimensionalState_zero, smul_zero]

theorem concreteGrowingThreeDimensionalState_transverse :
    WholeStateTransverse concreteGrowingThreeDimensionalState := by
  rw [concreteGrowingThreeDimensionalState_eq_neg_two_smul]
  exact wholeStateTransverse_real_smul _ _
    concreteThreeDimensionalState_transverse

theorem concreteGrowingThreeDimensionalState_reality :
    FiniteStateFourierReality concreteGrowingThreeDimensionalState := by
  intro wave
  rw [concreteGrowingThreeDimensionalState_eq_neg_two_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [concreteThreeDimensionalState_reality]
  funext coordinate
  simp [vectorConj]

def concreteGrowingThreeDimensionalSeed :
    SourceOwnedWholeRestartPhysicalSeed concreteGrowingViscosity where
  physicalState := concreteGrowingThreeDimensionalState
  physicalState_zero := concreteGrowingThreeDimensionalState_zero
  transverse := concreteGrowingThreeDimensionalState_transverse
  reality := concreteGrowingThreeDimensionalState_reality

def concreteGrowingThreeDimensionalReplay :=
  generatedWholeRestartCanonicalReplay concreteGrowingThreeDimensionalSeed

def concreteGrowingThreeDimensionalReceipt :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    concreteGrowingThreeDimensionalReplay

private theorem actualWholeProjectedTransversePath_zero
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    (actualWholeProjectedTransversePath receipt 0).1 = initialState := by
  change receipt.wholePath
      (Set.projIcc (0 : Real) requestedTime
        receipt.requestedTimePos.le 0) = initialState
  rw [Set.projIcc_of_mem receipt.requestedTimePos.le
    ⟨le_rfl, receipt.requestedTimePos.le⟩]
  exact receipt.wholePath_initial

private theorem actualWholeProjectedTransversePath_contact_time
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    (actualWholeProjectedTransversePath receipt contact.time.1).1 =
      contact.physicalState := by
  change receipt.wholePath
      (Set.projIcc (0 : Real) requestedTime
        receipt.requestedTimePos.le contact.time.1) =
    contact.physicalState
  rw [Set.projIcc_of_mem receipt.requestedTimePos.le contact.time.2]
  rfl

private theorem actualWholeProjectedTransversePath_prefix_terminal
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    (actualWholeProjectedTransversePath
      contact.prefixReceipt contact.time.1).1 =
        contact.physicalState := by
  change contact.prefixReceipt.wholePath
      (Set.projIcc (0 : Real) contact.time.1
        contact.time_pos.le contact.time.1) =
    contact.physicalState
  rw [Set.projIcc_of_mem contact.time_pos.le
    ⟨contact.time_pos.le, le_rfl⟩]
  exact contact.prefixReceipt_terminal

/-! ## Source-selected first cell crossing -/

theorem concreteGrowingThreeDimensionalSource_zero_not_mem :
    (0 : IntegerWavevector) ∉
      generatedSupport concreteGrowingThreeDimensionalSource := by
  decide

theorem concreteGrowingThreeDimensionalState_supported
    (wave : IntegerWavevector)
    (waveNotMem :
      wave ∉ generatedSupport concreteGrowingThreeDimensionalSource) :
    concreteGrowingThreeDimensionalState wave = 0 := by
  have baseNotMem :
      wave ∉ generatedSupport concreteThreeDimensionalSource := by
    simpa [concreteGrowingThreeDimensionalSource,
      concreteScaledThreeDimensionalSource] using waveNotMem
  rw [concreteGrowingThreeDimensionalState_eq_neg_two_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  have baseZero : concreteThreeDimensionalState wave = 0 := by
    simp [concreteThreeDimensionalState,
      generatedComplexVorticityState_apply, baseNotMem]
  rw [baseZero, smul_zero]

theorem concreteGrowingThreeDimensionalReceipt_state_zero :
    (actualWholeProjectedTransversePath
      concreteGrowingThreeDimensionalReceipt 0).1 =
        concreteGrowingThreeDimensionalState := by
  change concreteGrowingThreeDimensionalReceipt.wholePath
      (Set.projIcc (0 : Real)
        (wholeRestartDuration concreteGrowingThreeDimensionalSeed)
        concreteGrowingThreeDimensionalReceipt.requestedTimePos.le 0) =
    concreteGrowingThreeDimensionalState
  rw [Set.projIcc_of_mem
    concreteGrowingThreeDimensionalReceipt.requestedTimePos.le
    ⟨le_rfl, concreteGrowingThreeDimensionalReceipt.requestedTimePos.le⟩]
  exact concreteGrowingThreeDimensionalReceipt.wholePath_initial

theorem concreteGrowingThreeDimensionalReceipt_netPower_zero_eq_two :
    actualProjectedWholeNetEnstrophyPower
        concreteGrowingThreeDimensionalReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource) 0 = 2 := by
  let modes := generatedSupport concreteGrowingThreeDimensionalSource
  have nonlinearWorkEq :
      (∑ wave ∈ modes,
        complexCoordinateRealInner
          ((complexSharpSupportProjection modes
            concreteGrowingThreeDimensionalState) wave)
          (wholeStateVorticityNonlinearCoefficientAt
            concreteGrowingThreeDimensionalState wave)) =
        finiteStateVorticityNonlinearWork modes
          concreteGrowingThreeDimensionalState := by
    unfold finiteStateVorticityNonlinearWork
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      modes concreteGrowingThreeDimensionalState
      concreteGrowingThreeDimensionalState_supported wave]
  have viscousWorkEq :
      (∑ wave ∈ modes,
        complexCoordinateRealInner
          ((complexSharpSupportProjection modes
            concreteGrowingThreeDimensionalState) wave)
          ((concreteGrowingViscosity.coeff *
              integerWaveViscousMultiplier wave) •
            concreteGrowingThreeDimensionalState wave)) =
        concreteGrowingViscosity.coeff * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes
            concreteGrowingThreeDimensionalState := by
    calc
      (∑ wave ∈ modes,
          complexCoordinateRealInner
            ((complexSharpSupportProjection modes
              concreteGrowingThreeDimensionalState) wave)
            ((concreteGrowingViscosity.coeff *
                integerWaveViscousMultiplier wave) •
              concreteGrowingThreeDimensionalState wave)) =
          ∑ wave ∈ modes,
            complexCoordinateRealInner
              (concreteGrowingThreeDimensionalState wave)
              ((concreteGrowingViscosity.coeff *
                  integerWaveViscousMultiplier wave) •
                concreteGrowingThreeDimensionalState wave) := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [complexSharpSupportProjection_apply, if_pos waveMem]
      _ = _ := finiteStateVorticityViscousWork_eq
        modes concreteGrowingViscosity.coeff
          concreteGrowingThreeDimensionalState
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [concreteGrowingThreeDimensionalReceipt_state_zero]
  dsimp only
  rw [nonlinearWorkEq, viscousWorkEq]
  change
    2 * finiteStateVorticityNonlinearWork
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingThreeDimensionalState -
      2 * (concreteGrowingViscosity.coeff * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingThreeDimensionalState) = 2
  rw [concreteGrowingThreeDimensionalState_fullNonlinearWork_eq_two,
    concreteGrowingThreeDimensionalState_enstrophyMass_eq_fourteen]
  change
    2 * 2 -
      2 * ((1 / ((2 * Real.pi) ^ 2 * 14)) *
        (2 * Real.pi) ^ 2 * 14) = 2
  field_simp [Real.pi_ne_zero]
  norm_num

theorem concreteGrowingThreeDimensionalReceipt_netPower_initial_persistence :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Set.Icc (0 : Real)
          (wholeRestartDuration concreteGrowingThreeDimensionalSeed),
        actual < epsilon →
          (1 : Real) <
            actualProjectedWholeNetEnstrophyPower
              concreteGrowingThreeDimensionalReceipt
              (generatedSupport concreteGrowingThreeDimensionalSource)
              actual := by
  let netPower : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower
      concreteGrowingThreeDimensionalReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource) actual
  have netPowerContinuous : Continuous netPower :=
    actualProjectedWholeNetEnstrophyPower_continuous
      concreteGrowingThreeDimensionalReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource)
  have netPowerZero : netPower 0 = 2 := by
    exact concreteGrowingThreeDimensionalReceipt_netPower_zero_eq_two
  have neighborhoodOpen : IsOpen {actual | (1 : Real) < netPower actual} :=
    isOpen_lt continuous_const netPowerContinuous
  have zeroMem : 0 ∈ {actual | (1 : Real) < netPower actual} := by
    change (1 : Real) < netPower 0
    rw [netPowerZero]
    norm_num
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

def concreteGrowingNetPowerPersistenceTime : Real :=
  Classical.choose
    concreteGrowingThreeDimensionalReceipt_netPower_initial_persistence

theorem concreteGrowingNetPowerPersistenceTime_pos :
    0 < concreteGrowingNetPowerPersistenceTime :=
  (Classical.choose_spec
    concreteGrowingThreeDimensionalReceipt_netPower_initial_persistence).1

theorem concreteGrowingNetPowerPersistenceTime_spec
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration concreteGrowingThreeDimensionalSeed))
    (actualLt : actual < concreteGrowingNetPowerPersistenceTime) :
    (1 : Real) <
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingThreeDimensionalReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource)
        actual :=
  (Classical.choose_spec
    concreteGrowingThreeDimensionalReceipt_netPower_initial_persistence).2
      actual actualMem actualLt

def concreteGrowingShortDuration : Real :=
  min (wholeRestartDuration concreteGrowingThreeDimensionalSeed)
      concreteGrowingNetPowerPersistenceTime / 2

theorem concreteGrowingShortDuration_pos :
    0 < concreteGrowingShortDuration := by
  unfold concreteGrowingShortDuration
  exact div_pos
    (lt_min (wholeRestartDuration_pos concreteGrowingThreeDimensionalSeed)
      concreteGrowingNetPowerPersistenceTime_pos)
    (by norm_num)

theorem concreteGrowingShortDuration_le_original :
    concreteGrowingShortDuration ≤
      wholeRestartDuration concreteGrowingThreeDimensionalSeed := by
  unfold concreteGrowingShortDuration
  have minLe := min_le_left
    (wholeRestartDuration concreteGrowingThreeDimensionalSeed)
    concreteGrowingNetPowerPersistenceTime
  have minPos : 0 < min
      (wholeRestartDuration concreteGrowingThreeDimensionalSeed)
      concreteGrowingNetPowerPersistenceTime :=
    lt_min (wholeRestartDuration_pos concreteGrowingThreeDimensionalSeed)
      concreteGrowingNetPowerPersistenceTime_pos
  nlinarith

theorem concreteGrowingShortDuration_lt_persistence :
    concreteGrowingShortDuration <
      concreteGrowingNetPowerPersistenceTime := by
  unfold concreteGrowingShortDuration
  have minLe := min_le_right
    (wholeRestartDuration concreteGrowingThreeDimensionalSeed)
    concreteGrowingNetPowerPersistenceTime
  nlinarith [concreteGrowingNetPowerPersistenceTime_pos]

def concreteGrowingShortReceipt :
    WholeContinuousMildSerrinReceipt concreteGrowingViscosity
      concreteGrowingThreeDimensionalState concreteGrowingShortDuration :=
  restrictWholeContinuousMildSerrinReceipt
    concreteGrowingShortDuration_pos
    concreteGrowingShortDuration_le_original
    concreteGrowingThreeDimensionalReceipt

def concreteGrowingShortContact :=
  generatedPositiveWholeRestartContact concreteGrowingShortReceipt

def concreteGrowingShortCurrent :
    GeneratedWholeRestartCurrent concreteGrowingViscosity where
  initialState := concreteGrowingThreeDimensionalState
  duration := concreteGrowingShortDuration
  receipt := concreteGrowingShortReceipt
  contact := concreteGrowingShortContact

theorem concreteGrowingThreeDimensionalReceipt_mass_le_ceiling
    (time : Set.Icc (0 : Real)
      (wholeRestartDuration concreteGrowingThreeDimensionalSeed)) :
    wholeVorticityEuclideanMass
        (concreteGrowingThreeDimensionalReceipt.wholePath time) ≤
      wholeRestartCoefficientCeiling concreteGrowingThreeDimensionalSeed := by
  apply continuous_le_of_ae_le_commonTime
    concreteGrowingThreeDimensionalReceipt.requestedTimePos
    (fun actual => wholeVorticityEuclideanMass
      (concreteGrowingThreeDimensionalReceipt.wholePath actual))
    (wholeReceiptVorticityMass_continuous
      concreteGrowingThreeDimensionalReceipt)
  simpa only [concreteGrowingThreeDimensionalReceipt,
    concreteGrowingThreeDimensionalReplay] using
    generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
      concreteGrowingThreeDimensionalReplay

theorem concreteGrowingThreeDimensionalSeed_level_eq_eleven :
    wholeRestartCoefficientLevel concreteGrowingThreeDimensionalSeed = 11 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  change Nat.ceil
    (wholeVorticityEuclideanMass concreteGrowingThreeDimensionalState + 1) = 11
  rw [concreteGrowingThreeDimensionalState_wholeMass_eq_ten]
  norm_num

theorem concreteGrowingThreeDimensionalSeed_ceiling_eq_eleven :
    wholeRestartCoefficientCeiling concreteGrowingThreeDimensionalSeed = 11 := by
  unfold wholeRestartCoefficientCeiling
  rw [concreteGrowingThreeDimensionalSeed_level_eq_eleven]
  norm_num

def concreteGrowingShortContactOriginalTime :
    Set.Icc (0 : Real)
      (wholeRestartDuration concreteGrowingThreeDimensionalSeed) :=
  commonTimeInclusion concreteGrowingShortDuration_le_original
    concreteGrowingShortContact.time

theorem concreteGrowingShortContact_mass_le_eleven :
    wholeVorticityEuclideanMass
        concreteGrowingShortContact.physicalState ≤ 11 := by
  change wholeVorticityEuclideanMass
      (concreteGrowingThreeDimensionalReceipt.wholePath
        concreteGrowingShortContactOriginalTime) ≤ 11
  rw [← concreteGrowingThreeDimensionalSeed_ceiling_eq_eleven]
  exact concreteGrowingThreeDimensionalReceipt_mass_le_ceiling
    concreteGrowingShortContactOriginalTime

theorem concreteGrowingShortContact_prefix_netPower_gt_one
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      concreteGrowingShortContact.time.1) :
    (1 : Real) <
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingShortContact.prefixReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource)
        actual := by
  have actualLeShort : actual ≤ concreteGrowingShortDuration :=
    actualMem.2.trans concreteGrowingShortContact.time.2.2
  have actualMemOriginal : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration concreteGrowingThreeDimensionalSeed) :=
    ⟨actualMem.1,
      actualLeShort.trans concreteGrowingShortDuration_le_original⟩
  have actualLtPersistence :
      actual < concreteGrowingNetPowerPersistenceTime :=
    actualLeShort.trans_lt concreteGrowingShortDuration_lt_persistence
  have stateEq :
      (actualWholeProjectedTransversePath
        concreteGrowingShortContact.prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath
        concreteGrowingThreeDimensionalReceipt actual).1 := by
    change concreteGrowingShortContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) concreteGrowingShortContact.time.1
          concreteGrowingShortContact.time_pos.le actual) =
      concreteGrowingThreeDimensionalReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration concreteGrowingThreeDimensionalSeed)
          concreteGrowingThreeDimensionalReceipt.requestedTimePos.le actual)
    rw [Set.projIcc_of_mem
      concreteGrowingShortContact.time_pos.le actualMem]
    rw [Set.projIcc_of_mem
      concreteGrowingThreeDimensionalReceipt.requestedTimePos.le
      actualMemOriginal]
    rfl
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortContact.prefixReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource)
          actual =
        actualProjectedWholeNetEnstrophyPower
          concreteGrowingThreeDimensionalReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource)
          actual := by
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [stateEq]
  rw [powerEq]
  exact concreteGrowingNetPowerPersistenceTime_spec
    actual actualMemOriginal actualLtPersistence

theorem concreteGrowingShortContact_prefix_netPower_integral_pos :
    0 < ∫ actual in (0 : Real)..concreteGrowingShortContact.time.1,
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingShortContact.prefixReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource)
        actual := by
  have lower := intervalIntegral.integral_mono_on
    (f := fun _actual : Real => (1 : Real))
    (g := actualProjectedWholeNetEnstrophyPower
      concreteGrowingShortContact.prefixReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource))
    (μ := volume)
    concreteGrowingShortContact.time_pos.le
    (continuous_const.intervalIntegrable
      0 concreteGrowingShortContact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      concreteGrowingShortContact.prefixReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource)
      ).intervalIntegrable 0 concreteGrowingShortContact.time.1)
    (fun actual actualMem =>
      (concreteGrowingShortContact_prefix_netPower_gt_one
        actual actualMem).le)
  have constantIntegral :
      (∫ _actual in (0 : Real)..concreteGrowingShortContact.time.1,
        (1 : Real)) = concreteGrowingShortContact.time.1 := by
    simp
  rw [constantIntegral] at lower
  exact concreteGrowingShortContact.time_pos.trans_le lower

theorem concreteGrowingThreeDimensionalState_finiteMass_eq_ten :
    finiteStateVorticityCoefficientEnstrophy
        (generatedSupport concreteGrowingThreeDimensionalSource)
        concreteGrowingThreeDimensionalState = 10 := by
  rw [← wholeVorticityEuclideanMass_eq_finite_of_supported
    (generatedSupport concreteGrowingThreeDimensionalSource)
    concreteGrowingThreeDimensionalState
    concreteGrowingThreeDimensionalState_supported]
  exact concreteGrowingThreeDimensionalState_wholeMass_eq_ten

theorem concreteGrowingShortContact_finiteMass_gt_ten :
    (10 : Real) <
      finiteStateVorticityCoefficientEnstrophy
        (generatedSupport concreteGrowingThreeDimensionalSource)
        concreteGrowingShortContact.physicalState := by
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      concreteGrowingShortContact.prefixReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource)
      concreteGrowingThreeDimensionalSource_zero_not_mem
  rw [concreteGrowingShortContact.prefixReceipt_terminal,
    concreteGrowingThreeDimensionalState_finiteMass_eq_ten] at ledger
  linarith [concreteGrowingShortContact_prefix_netPower_integral_pos]

theorem concreteGrowingShortContact_mass_gt_ten :
    (10 : Real) <
      wholeVorticityEuclideanMass concreteGrowingShortContact.physicalState := by
  exact concreteGrowingShortContact_finiteMass_gt_ten.trans_le
    (SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      (generatedSupport concreteGrowingThreeDimensionalSource)
      concreteGrowingShortContact.physicalState)

theorem concreteGrowingShortContact_level_eq_twelve :
    wholeRestartCoefficientLevel concreteGrowingShortContact = 12 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  rw [Nat.ceil_eq_iff (by norm_num : (12 : Nat) ≠ 0)]
  norm_num
  constructor
  · linarith [concreteGrowingShortContact_mass_gt_ten]
  · linarith [concreteGrowingShortContact_mass_le_eleven]

/-- The source-selected first occurrence crosses exactly one quantized cell;
this is the finite seed required by any recursive regeneration invariant. -/
theorem concreteGrowingShortCurrent_initial_cell_crossing :
    wholeRestartCoefficientLevel concreteGrowingShortContact =
      wholeRestartCoefficientLevel concreteGrowingThreeDimensionalSeed + 1 := by
  rw [concreteGrowingShortContact_level_eq_twelve,
    concreteGrowingThreeDimensionalSeed_level_eq_eleven]

/-! ## Exact regeneration probe on the fixed native successor -/

theorem concreteGrowingShortCurrent_nextReceipt_state_zero :
    (actualWholeProjectedTransversePath
      concreteGrowingShortCurrent.nextReceipt 0).1 =
        concreteGrowingShortContact.physicalState := by
  have zeroState :=
    actualWholeProjectedTransversePath_zero
      concreteGrowingShortCurrent.nextReceipt
  simpa only [concreteGrowingShortCurrent] using zeroState

theorem concreteGrowingShortContact_prefix_state_terminal :
    (actualWholeProjectedTransversePath
      concreteGrowingShortContact.prefixReceipt
      concreteGrowingShortContact.time.1).1 =
        concreteGrowingShortContact.physicalState :=
  actualWholeProjectedTransversePath_prefix_terminal
    concreteGrowingShortContact

/-- The positive scale-relative source instruction survives the first
write-back and is present at time zero of the exact native `.next` receipt. -/
theorem concreteGrowingShortCurrent_nextReceipt_netPower_zero_gt_one :
    (1 : Real) <
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingShortCurrent.nextReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource) 0 := by
  have terminalPositive :=
    concreteGrowingShortContact_prefix_netPower_gt_one
      concreteGrowingShortContact.time.1
      ⟨concreteGrowingShortContact.time_pos.le, le_rfl⟩
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortCurrent.nextReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource) 0 =
        actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortContact.prefixReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingShortContact.time.1 := by
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [concreteGrowingShortCurrent_nextReceipt_state_zero,
      concreteGrowingShortContact_prefix_state_terminal]
  rwa [powerEq]

theorem concreteGrowingShortCurrent_nextReceipt_netPower_persistence :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Set.Icc (0 : Real)
          (wholeRestartDuration concreteGrowingShortContact),
        actual < epsilon →
          (1 : Real) <
            actualProjectedWholeNetEnstrophyPower
              concreteGrowingShortCurrent.nextReceipt
              (generatedSupport concreteGrowingThreeDimensionalSource)
              actual := by
  let netPower : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower
      concreteGrowingShortCurrent.nextReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource) actual
  have netPowerContinuous : Continuous netPower :=
    actualProjectedWholeNetEnstrophyPower_continuous
      concreteGrowingShortCurrent.nextReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource)
  have zeroMem : 0 ∈ {actual | (1 : Real) < netPower actual} := by
    exact concreteGrowingShortCurrent_nextReceipt_netPower_zero_gt_one
  have neighborhoodOpen : IsOpen {actual | (1 : Real) < netPower actual} :=
    isOpen_lt continuous_const netPowerContinuous
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

def concreteGrowingNextNetPowerPersistenceTime : Real :=
  Classical.choose
    concreteGrowingShortCurrent_nextReceipt_netPower_persistence

theorem concreteGrowingNextNetPowerPersistenceTime_pos :
    0 < concreteGrowingNextNetPowerPersistenceTime :=
  (Classical.choose_spec
    concreteGrowingShortCurrent_nextReceipt_netPower_persistence).1

theorem concreteGrowingNextNetPowerPersistenceTime_spec
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration concreteGrowingShortContact))
    (actualLt : actual < concreteGrowingNextNetPowerPersistenceTime) :
    (1 : Real) <
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingShortCurrent.nextReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource)
        actual :=
  (Classical.choose_spec
    concreteGrowingShortCurrent_nextReceipt_netPower_persistence).2
      actual actualMem actualLt

/-- The fixed compiler either keeps its selected successor inside the
regenerated sign window or exposes the exact horizon mismatch. -/
theorem concreteGrowingShortCurrent_nextContact_netPower_or_horizon_mismatch :
    (1 : Real) <
        actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortCurrent.nextContact.prefixReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingShortCurrent.nextContact.time.1 ∨
      concreteGrowingNextNetPowerPersistenceTime ≤
        concreteGrowingShortCurrent.nextContact.time.1 := by
  by_cases inside :
      concreteGrowingShortCurrent.nextContact.time.1 <
        concreteGrowingNextNetPowerPersistenceTime
  · left
    have sourcePositive :=
      concreteGrowingNextNetPowerPersistenceTime_spec
        concreteGrowingShortCurrent.nextContact.time.1
        ⟨concreteGrowingShortCurrent.nextContact.time_pos.le,
          concreteGrowingShortCurrent.nextContact.time.2.2⟩ inside
    have stateEq :
        (actualWholeProjectedTransversePath
          concreteGrowingShortCurrent.nextContact.prefixReceipt
          concreteGrowingShortCurrent.nextContact.time.1).1 =
        (actualWholeProjectedTransversePath
          concreteGrowingShortCurrent.nextReceipt
          concreteGrowingShortCurrent.nextContact.time.1).1 := by
      calc
        (actualWholeProjectedTransversePath
            concreteGrowingShortCurrent.nextContact.prefixReceipt
            concreteGrowingShortCurrent.nextContact.time.1).1 =
            concreteGrowingShortCurrent.nextContact.physicalState :=
          actualWholeProjectedTransversePath_prefix_terminal
            concreteGrowingShortCurrent.nextContact
        _ = (actualWholeProjectedTransversePath
              concreteGrowingShortCurrent.nextReceipt
              concreteGrowingShortCurrent.nextContact.time.1).1 :=
          (actualWholeProjectedTransversePath_contact_time
            concreteGrowingShortCurrent.nextContact).symm
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [stateEq]
    exact sourcePositive
  · right
    exact le_of_not_gt inside

def concreteGrowingNextFiniteCellDeficit : Real :=
  11 - finiteStateVorticityCoefficientEnstrophy
    (generatedSupport concreteGrowingThreeDimensionalSource)
    concreteGrowingShortContact.physicalState

theorem concreteGrowingShortCurrent_level_zero_eq_twelve :
    restartCoefficientLevelNat concreteGrowingShortCurrent 0 = 12 := by
  unfold restartCoefficientLevelNat
  rw [run_zero]
  change wholeRestartCoefficientLevel concreteGrowingShortContact = 12
  exact concreteGrowingShortContact_level_eq_twelve

theorem concreteGrowingShortCurrent_next_level_add_one_iff_mass_gt_eleven :
    restartCoefficientLevelNat concreteGrowingShortCurrent 1 =
          restartCoefficientLevelNat concreteGrowingShortCurrent 0 + 1 ↔
      (11 : Real) <
        restartPhysicalVorticityMass concreteGrowingShortCurrent 1 := by
  have crossing :=
    restartCoefficientLevelNat_succ_eq_add_one_iff_mass_crosses_cell
      concreteGrowingShortCurrent 0
  rw [concreteGrowingShortCurrent_level_zero_eq_twelve] at crossing
  norm_num at crossing
  constructor
  · intro levelEq
    have levelEq' :
        restartCoefficientLevelNat concreteGrowingShortCurrent 1 = 13 := by
      rw [concreteGrowingShortCurrent_level_zero_eq_twelve] at levelEq
      norm_num at levelEq ⊢
      exact levelEq
    exact crossing.mp levelEq'
  · intro massGt
    have levelEq := crossing.mpr massGt
    rw [concreteGrowingShortCurrent_level_zero_eq_twelve]
    norm_num
    exact levelEq

theorem concreteGrowingShortCurrent_next_finiteNetIntegral_eq_gain :
    (∫ actual in (0 : Real)..
        concreteGrowingShortCurrent.nextContact.time.1,
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingShortCurrent.nextContact.prefixReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource)
        actual) =
      finiteStateVorticityCoefficientEnstrophy
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingShortCurrent.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport concreteGrowingThreeDimensionalSource)
          concreteGrowingShortContact.physicalState := by
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      concreteGrowingShortCurrent.nextContact.prefixReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource)
      concreteGrowingThreeDimensionalSource_zero_not_mem
  rw [concreteGrowingShortCurrent.nextContact.prefixReceipt_terminal] at ledger
  simpa only [concreteGrowingShortCurrent] using ledger

/-- The exact finite deficit is sufficient for the next whole-state cell
crossing; no tail estimate is needed because endpoint whole mass dominates
the same finite projected ledger. -/
theorem concreteGrowingShortCurrent_next_cell_crossing_of_finiteDebit
    (finiteDebit :
      concreteGrowingNextFiniteCellDeficit <
        ∫ actual in (0 : Real)..
          concreteGrowingShortCurrent.nextContact.time.1,
        actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortCurrent.nextContact.prefixReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource)
          actual) :
    restartCoefficientLevelNat concreteGrowingShortCurrent 1 =
      restartCoefficientLevelNat concreteGrowingShortCurrent 0 + 1 := by
  apply
    restartCoefficientLevelNat_succ_eq_add_one_via_cellIncidence_of_projectedNetDebit
      concreteGrowingShortCurrent 0
      (generatedSupport concreteGrowingThreeDimensionalSource)
      concreteGrowingThreeDimensionalSource_zero_not_mem
  rw [concreteGrowingShortCurrent_level_zero_eq_twelve]
  norm_num
  change concreteGrowingNextFiniteCellDeficit <
    ∫ actual in (0 : Real)..
      concreteGrowingShortCurrent.nextContact.time.1,
      actualProjectedWholeNetEnstrophyPower
        concreteGrowingShortCurrent.nextContact.prefixReceipt
        (generatedSupport concreteGrowingThreeDimensionalSource) actual
  exact finiteDebit

/-- The regenerated source instruction closes the next exact cell whenever
the fixed compiler time lies inside its persistence window and pays the
finite deficit.  Both hypotheses are now explicit source equations, not
future recurrence or summability assumptions. -/
theorem concreteGrowingShortCurrent_next_cell_crossing_of_compiler_alignment
    (inside : concreteGrowingShortCurrent.nextContact.time.1 <
      concreteGrowingNextNetPowerPersistenceTime)
    (paysDeficit : concreteGrowingNextFiniteCellDeficit <
      concreteGrowingShortCurrent.nextContact.time.1) :
    restartCoefficientLevelNat concreteGrowingShortCurrent 1 =
      restartCoefficientLevelNat concreteGrowingShortCurrent 0 + 1 := by
  apply concreteGrowingShortCurrent_next_cell_crossing_of_finiteDebit
  have pointwise :
      ∀ actual ∈ Set.Icc (0 : Real)
          concreteGrowingShortCurrent.nextContact.time.1,
        (1 : Real) <
          actualProjectedWholeNetEnstrophyPower
            concreteGrowingShortCurrent.nextContact.prefixReceipt
            (generatedSupport concreteGrowingThreeDimensionalSource)
            actual := by
    intro actual actualMem
    have actualMemSource : actual ∈ Set.Icc (0 : Real)
        (wholeRestartDuration concreteGrowingShortContact) :=
      ⟨actualMem.1,
        actualMem.2.trans
          concreteGrowingShortCurrent.nextContact.time.2.2⟩
    have actualLt : actual <
        concreteGrowingNextNetPowerPersistenceTime :=
      actualMem.2.trans_lt inside
    have sourcePositive :=
      concreteGrowingNextNetPowerPersistenceTime_spec
        actual actualMemSource actualLt
    have stateEq :
        (actualWholeProjectedTransversePath
          concreteGrowingShortCurrent.nextContact.prefixReceipt actual).1 =
        (actualWholeProjectedTransversePath
          concreteGrowingShortCurrent.nextReceipt actual).1 := by
      change concreteGrowingShortCurrent.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real)
            concreteGrowingShortCurrent.nextContact.time.1
            concreteGrowingShortCurrent.nextContact.time_pos.le actual) =
        concreteGrowingShortCurrent.nextReceipt.wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration concreteGrowingShortCurrent.contact)
            concreteGrowingShortCurrent.nextReceipt.requestedTimePos.le actual)
      rw [Set.projIcc_of_mem
        concreteGrowingShortCurrent.nextContact.time_pos.le actualMem]
      rw [Set.projIcc_of_mem
        concreteGrowingShortCurrent.nextReceipt.requestedTimePos.le
        actualMemSource]
      rfl
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [stateEq]
    exact sourcePositive
  have lower := intervalIntegral.integral_mono_on
    (μ := volume)
    concreteGrowingShortCurrent.nextContact.time_pos.le
    (continuous_const.intervalIntegrable 0
      concreteGrowingShortCurrent.nextContact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      concreteGrowingShortCurrent.nextContact.prefixReceipt
      (generatedSupport concreteGrowingThreeDimensionalSource)
      ).intervalIntegrable 0
        concreteGrowingShortCurrent.nextContact.time.1)
    (fun actual actualMem => (pointwise actual actualMem).le)
  have normalized :
      concreteGrowingShortCurrent.nextContact.time.1 ≤
        ∫ actual in (0 : Real)..
          concreteGrowingShortCurrent.nextContact.time.1,
        actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortCurrent.nextContact.prefixReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource)
          actual := by
    simpa [intervalIntegral.integral_const, smul_eq_mul] using lower
  exact paysDeficit.trans_le normalized

/-! ## Source-generated moving regeneration inventory -/

/-- The concrete source support is the initial physical inventory.  Every
successor extends it by the canonical local kernel core generated at that
actual run occurrence.  No cutoff sequence or future table is supplied. -/
noncomputable def concreteGrowingRegenerationInventory :
    Nat → Finset IntegerWavevector
  | 0 => generatedSupport concreteGrowingThreeDimensionalSource
  | stage + 1 =>
      concreteGrowingRegenerationInventory stage ∪
        (sourceOwnedLocalKernelCore concreteGrowingViscosity
          (restartCoefficientCeiling concreteGrowingShortCurrent
            (stage + 1))).erase 0

theorem concreteGrowingRegenerationInventory_zeroNotMem :
    ∀ stage,
      (0 : IntegerWavevector) ∉
        concreteGrowingRegenerationInventory stage := by
  intro stage
  induction stage with
  | zero =>
      exact concreteGrowingThreeDimensionalSource_zero_not_mem
  | succ stage inductionHypothesis =>
      simp [concreteGrowingRegenerationInventory, inductionHypothesis]

theorem concreteGrowingRegenerationInventory_nested
    (stage : Nat) :
    concreteGrowingRegenerationInventory stage ⊆
      concreteGrowingRegenerationInventory (stage + 1) := by
  rw [concreteGrowingRegenerationInventory]
  exact Finset.subset_union_left

theorem concreteGrowingRegenerationInventory_initialFiniteMass_eq_ten :
    finiteStateVorticityCoefficientEnstrophy
        (concreteGrowingRegenerationInventory 0)
        concreteGrowingShortCurrent.initialState = 10 := by
  change
    finiteStateVorticityCoefficientEnstrophy
        (generatedSupport concreteGrowingThreeDimensionalSource)
        concreteGrowingThreeDimensionalState = 10
  exact concreteGrowingThreeDimensionalState_finiteMass_eq_ten

/-- The candidate invariant's first actual edge is paid by the exact source
net action, with any newly exposed kernel material retained as an additional
nonnegative incidence row. -/
theorem concreteGrowingRegenerationInventory_edgePayment_zero_pos :
    0 < runMovingInventoryEdgePayment concreteGrowingShortCurrent
      concreteGrowingRegenerationInventory 0 := by
  have actionPos :
      0 < ∫ actual in (0 : Real)..
          (run concreteGrowingShortCurrent 0).contact.time.1,
        actualProjectedWholeNetEnstrophyPower
          (run concreteGrowingShortCurrent 0).contact.prefixReceipt
          (concreteGrowingRegenerationInventory 0) actual := by
    change
      0 < ∫ actual in (0 : Real)..
          concreteGrowingShortContact.time.1,
        actualProjectedWholeNetEnstrophyPower
          concreteGrowingShortContact.prefixReceipt
          (generatedSupport concreteGrowingThreeDimensionalSource) actual
    exact concreteGrowingShortContact_prefix_netPower_integral_pos
  have captureNonneg :
      0 ≤ wholeInventoryCaptureMass
        (concreteGrowingRegenerationInventory 0)
        (concreteGrowingRegenerationInventory 1)
        (run concreteGrowingShortCurrent 1).initialState :=
    wholeInventoryCaptureMass_nonneg_of_subset
      (concreteGrowingRegenerationInventory_nested 0)
      (run concreteGrowingShortCurrent 1).initialState
  unfold runMovingInventoryEdgePayment
  exact add_pos_of_pos_of_nonneg actionPos captureNonneg

/-- First generated advance of the scale-relative profile.  This statement
is a readout of the actual edge payment equation, not a supplied endpoint
mass or cell-crossing premise. -/
theorem concreteGrowingRegenerationInventory_firstBoundaryMass_gt_ten :
    (10 : Real) <
      finiteStateVorticityCoefficientEnstrophy
        (concreteGrowingRegenerationInventory 1)
        (run concreteGrowingShortCurrent 1).initialState := by
  have edgeEq :=
    runMovingInventoryEdgePayment_eq_nextFiniteMass_sub_current
      concreteGrowingShortCurrent concreteGrowingRegenerationInventory
      concreteGrowingRegenerationInventory_zeroNotMem 0
  simp only [Nat.zero_add, run_zero] at edgeEq
  rw [concreteGrowingRegenerationInventory_initialFiniteMass_eq_ten] at edgeEq
  linarith [concreteGrowingRegenerationInventory_edgePayment_zero_pos]

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteCellRegeneration
end NavierStokes
end SaturationMonoid
