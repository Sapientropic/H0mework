import H0mework.NavierStokes.Accumulation.ConcreteCellRegeneration
import H0mework.NavierStokes.Crossing.GluingNegativeOneBridge
import H0mework.NavierStokes.KineticRestart.ExactKineticDissipation
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation

/-!
# Concrete two-scale lift source

This file compiles one reality-closed, genuinely three-dimensional two-scale
Fourier occurrence and keeps both sides of its first whole-NS update visible.
The source has exact mass, gradient mass and nonlinear work, while one
explicit off-support row proves that the actual nonlinear tangent expands the
finite carrier.  Thus the new row is material for a moving packet lineage; it
cannot be discarded by resetting to the original finite table.

No future recurrence, contact choice, mass debit, branch, or summability
certificate is accepted by this source calculation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open scoped BigOperators Matrix Topology

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteTwoScaleLiftSource

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientRawSourceInitialCriticalLoad
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteCellRegeneration
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteThreeDimensionalSource
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open Filter

noncomputable section

abbrev p₁ : IntegerWavevector := ![1, 0, 0]
abbrev q₁ : IntegerWavevector := ![0, 1, 0]
abbrev r₁ : IntegerWavevector := ![-1, -1, 0]
abbrev l₁ : IntegerWavevector := ![0, 0, 1]
abbrev p₂ : IntegerWavevector := ![2, 0, 0]
abbrev q₂ : IntegerWavevector := ![0, 2, 0]
abbrev r₂ : IntegerWavevector := ![-2, -2, 0]
abbrev l₂ : IntegerWavevector := ![0, 0, 2]

def raw (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave = p₁ then ![0, -2, 0]
  else if wave = q₁ then ![0, 0, -2]
  else if wave = r₁ then ![-2, 2, 0]
  else if wave = l₁ then ![-2, 0, 0]
  else if wave = p₂ then ![0, -8, 0]
  else if wave = q₂ then ![0, 0, -8]
  else if wave = r₂ then ![-8, 8, 0]
  else if wave = l₂ then ![-8, 0, 0]
  else 0

def source : RawVorticityFourierSource where
  activeModes := {p₁, q₁, r₁, l₁, p₂, q₂, r₂, l₂}
  rawVorticity := raw

def modes : Finset IntegerWavevector :=
  {p₁, q₁, r₁, l₁, p₂, q₂, r₂, l₂,
    waveNeg p₁, waveNeg q₁, waveNeg r₁, waveNeg l₁,
    waveNeg p₂, waveNeg q₂, waveNeg r₂, waveNeg l₂}

theorem source_support_eq_modes : generatedSupport source = modes := by decide

def state : ComplexVorticityHilbertState :=
  generatedComplexVorticityState source modes

theorem zero_not_mem : (0 : IntegerWavevector) ∉ generatedSupport source := by
  decide

theorem supported
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ modes) :
    state wave = 0 := by
  simp [state, generatedComplexVorticityState_apply, waveNotMem]

theorem state_zero : state 0 = 0 := by
  exact supported 0 (by decide)

theorem state_transverse : WholeStateTransverse state := by
  intro wave
  by_cases waveMem : wave ∈ modes
  · rw [state, generatedComplexVorticityState_apply, if_pos waveMem]
    exact generatedVorticityCoefficient_transverse source wave
  · rw [supported wave waveMem, dotProduct_zero]

theorem state_reality : FiniteStateFourierReality state := by
  intro wave
  unfold state
  simp only [generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ modes
  · have negMem : waveNeg wave ∈ modes := by
      rw [← source_support_eq_modes] at waveMem ⊢
      exact generatedSupport_waveNeg_mem source waveMem
    rw [if_pos waveMem, if_pos negMem,
      generatedVorticityCoefficient_waveNeg]
  · have negNotMem : waveNeg wave ∉ modes := by
      intro negMem
      apply waveMem
      have originalMem : waveNeg (waveNeg wave) ∈ modes := by
        rw [← source_support_eq_modes] at negMem ⊢
        exact generatedSupport_waveNeg_mem source negMem
      simpa using originalMem
    rw [if_neg waveMem, if_neg negNotMem, vectorConj_zero]

theorem state_p₁ : state p₁ = ![0, -1, 0] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem state_q₁ : state q₁ = ![0, 0, -1] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem state_r₁ : state r₁ = ![-1, 1, 0] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem state_l₁ : state l₁ = ![-1, 0, 0] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem state_p₂ : state p₂ = ![0, -4, 0] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
    norm_num

theorem state_q₂ : state q₂ = ![0, 0, -4] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
    norm_num

theorem state_r₂ : state r₂ = ![-4, 4, 0] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    norm_num

theorem state_l₂ : state l₂ = ![-4, 0, 0] := by
  rw [state, generatedComplexVorticityState_apply]
  rw [if_pos (by decide)]
  unfold generatedVorticityCoefficient
  rw [if_pos (by rw [source_support_eq_modes]; decide)]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, source, raw, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
    norm_num

theorem state_waveNeg_of_mem
    (wave : IntegerWavevector)
    (waveMem : wave ∈ modes)
    (negMem : waveNeg wave ∈ modes) :
    state (waveNeg wave) = vectorConj (state wave) := by
  simp only [state, generatedComplexVorticityState_apply,
    if_pos waveMem, if_pos negMem]
  exact generatedVorticityCoefficient_waveNeg source wave

theorem state_neg_p₁ : state ![-1, 0, 0] = ![0, -1, 0] := by
  have waveEq : (![-1, 0, 0] : IntegerWavevector) = waveNeg p₁ := by decide
  rw [waveEq, state_waveNeg_of_mem p₁ (by decide) (by decide), state_p₁]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_q₁ : state ![0, -1, 0] = ![0, 0, -1] := by
  have waveEq : (![0, -1, 0] : IntegerWavevector) = waveNeg q₁ := by decide
  rw [waveEq, state_waveNeg_of_mem q₁ (by decide) (by decide), state_q₁]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_r₁ : state ![1, 1, 0] = ![-1, 1, 0] := by
  have waveEq : (![1, 1, 0] : IntegerWavevector) = waveNeg r₁ := by decide
  rw [waveEq, state_waveNeg_of_mem r₁ (by decide) (by decide), state_r₁]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_l₁ : state ![0, 0, -1] = ![-1, 0, 0] := by
  have waveEq : (![0, 0, -1] : IntegerWavevector) = waveNeg l₁ := by decide
  rw [waveEq, state_waveNeg_of_mem l₁ (by decide) (by decide), state_l₁]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_p₂ : state ![-2, 0, 0] = ![0, -4, 0] := by
  have waveEq : (![-2, 0, 0] : IntegerWavevector) = waveNeg p₂ := by decide
  rw [waveEq, state_waveNeg_of_mem p₂ (by decide) (by decide), state_p₂]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_q₂ : state ![0, -2, 0] = ![0, 0, -4] := by
  have waveEq : (![0, -2, 0] : IntegerWavevector) = waveNeg q₂ := by decide
  rw [waveEq, state_waveNeg_of_mem q₂ (by decide) (by decide), state_q₂]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_r₂ : state ![2, 2, 0] = ![-4, 4, 0] := by
  have waveEq : (![2, 2, 0] : IntegerWavevector) = waveNeg r₂ := by decide
  rw [waveEq, state_waveNeg_of_mem r₂ (by decide) (by decide), state_r₂]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem state_neg_l₂ : state ![0, 0, -2] = ![-4, 0, 0] := by
  have waveEq : (![0, 0, -2] : IntegerWavevector) = waveNeg l₂ := by decide
  rw [waveEq, state_waveNeg_of_mem l₂ (by decide) (by decide), state_l₂]
  funext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem mass_eq : wholeVorticityEuclideanMass state = 170 := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    modes state supported]
  classical
  unfold finiteStateVorticityCoefficientEnstrophy
  simp [modes, state_p₁, state_q₁, state_r₁, state_l₁,
    state_p₂, state_q₂, state_r₂, state_l₂,
    state_neg_p₁, state_neg_q₁, state_neg_r₁, state_neg_l₁,
    state_neg_p₂, state_neg_q₂, state_neg_r₂, state_neg_l₂,
    waveNeg]
  norm_num [complexCoordinateVectorNormSq, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem gradientMass_eq :
    finiteStateVorticityEnstrophyMass modes state = 910 := by
  classical
  unfold finiteStateVorticityEnstrophyMass
  simp [modes, state_p₁, state_q₁, state_r₁, state_l₁,
    state_p₂, state_q₂, state_r₂, state_l₂,
    state_neg_p₁, state_neg_q₁, state_neg_r₁, state_neg_l₁,
    state_neg_p₂, state_neg_q₂, state_neg_r₂, state_neg_l₂,
    waveNeg]
  norm_num [integerWaveNormSq, complexCoordinateAmplitudeSq,
    complexCoordinateVectorNormSq, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

def crossScaleOutput : IntegerWavevector := ![2, -1, 0]

theorem crossScaleOutput_not_mem : crossScaleOutput ∉ modes := by decide

theorem crossScaleOutput_nonlinearCoefficient :
    finiteStateVorticityNonlinearCoefficientAt modes state crossScaleOutput =
      ![-4, -8, 0] := by
  classical
  unfold finiteStateVorticityNonlinearCoefficientAt
    finiteStateVorticityNonlinearPairContribution
    finiteStateVelocityCoefficient
    biotSavartVelocityCoefficient
  simp (config := { maxSteps := 1000000 })
    [modes, crossScaleOutput,
      state_p₁, state_q₁, state_r₁, state_l₁,
      state_p₂, state_q₂, state_r₂, state_l₂,
      state_neg_p₁, state_neg_q₁, state_neg_r₁, state_neg_l₁,
      state_neg_p₂, state_neg_q₂, state_neg_r₂, state_neg_l₂,
      waveNeg]
  constructor <;> try constructor
  all_goals
    norm_num [complexWavevector, integerWaveNormSq, dotProduct,
      cross_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Complex.div_im, Complex.div_re, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Real.pi_ne_zero, Complex.I_sq] <;>
    field_simp [Real.pi_ne_zero] <;>
    simp [Complex.I_sq] <;>
    ring

theorem crossScaleOutput_nonlinearCoefficient_ne_zero :
    finiteStateVorticityNonlinearCoefficientAt modes state crossScaleOutput ≠ 0 := by
  rw [crossScaleOutput_nonlinearCoefficient]
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [Matrix.cons_val_zero] at firstZero

theorem crossScaleOutput_wholeNonlinearCoefficient :
    wholeStateVorticityNonlinearCoefficientAt state crossScaleOutput =
      ![-4, -8, 0] := by
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    modes state supported crossScaleOutput]
  exact crossScaleOutput_nonlinearCoefficient

theorem crossScaleOutput_state_zero : state crossScaleOutput = 0 := by
  exact supported crossScaleOutput crossScaleOutput_not_mem

theorem crossScaleOutput_wholeTangent :
    wholeLatticeVorticityFourierTangentAt
        concreteGrowingViscosity.coeff state crossScaleOutput =
      ![-4, -8, 0] := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [crossScaleOutput_wholeNonlinearCoefficient,
    crossScaleOutput_state_zero, smul_zero, sub_zero]

/-- Strongest fresh high-frequency receiver in the complete two-scale
convolution.  Its squared lattice frequency is `20`, while every donor mode
has squared frequency at most `8`. -/
def highScaleOutput : IntegerWavevector := ![2, 4, 0]

theorem highScaleOutput_not_mem : highScaleOutput ∉ modes := by decide

theorem highScaleOutput_normSq_eq :
    integerWaveNormSq highScaleOutput = 20 := by
  norm_num [highScaleOutput, integerWaveNormSq,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

theorem donorModes_normSq_le_eight :
    ∀ wave ∈ modes, integerWaveNormSq wave ≤ 8 := by
  intro wave waveMem
  simp only [modes, Finset.mem_insert, Finset.mem_singleton] at waveMem
  rcases waveMem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [integerWaveNormSq, p₁, q₁, r₁, l₁,
      p₂, q₂, r₂, l₂, waveNeg,
      Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]

theorem donorMode_normSq_lt_highScale
    (wave : IntegerWavevector)
    (waveMem : wave ∈ modes) :
    integerWaveNormSq wave < integerWaveNormSq highScaleOutput := by
  rw [highScaleOutput_normSq_eq]
  exact (donorModes_normSq_le_eight wave waveMem).trans_lt (by norm_num)

theorem highScaleOutput_nonlinearCoefficient :
    finiteStateVorticityNonlinearCoefficientAt modes state highScaleOutput =
      ![32, -16, 0] := by
  classical
  unfold finiteStateVorticityNonlinearCoefficientAt
    finiteStateVorticityNonlinearPairContribution
    finiteStateVelocityCoefficient
    biotSavartVelocityCoefficient
  simp (config := { maxSteps := 1000000 })
    [modes, highScaleOutput,
      state_p₁, state_q₁, state_r₁, state_l₁,
      state_p₂, state_q₂, state_r₂, state_l₂,
      state_neg_p₁, state_neg_q₁, state_neg_r₁, state_neg_l₁,
      state_neg_p₂, state_neg_q₂, state_neg_r₂, state_neg_l₂,
      waveNeg]
  constructor <;> try constructor
  all_goals
    norm_num [complexWavevector, integerWaveNormSq, dotProduct,
      cross_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Complex.div_im, Complex.div_re, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Real.pi_ne_zero, Complex.I_sq] <;>
    field_simp [Real.pi_ne_zero] <;>
    simp [Complex.I_sq] <;>
    ring

theorem highScaleOutput_wholeTangent :
    wholeLatticeVorticityFourierTangentAt
        concreteGrowingViscosity.coeff state highScaleOutput =
      ![32, -16, 0] := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    modes state supported highScaleOutput]
  rw [highScaleOutput_nonlinearCoefficient,
    supported highScaleOutput highScaleOutput_not_mem,
    smul_zero, sub_zero]

theorem highScaleOutput_wholeTangent_ne_zero :
    wholeLatticeVorticityFourierTangentAt
        concreteGrowingViscosity.coeff state highScaleOutput ≠ 0 := by
  rw [highScaleOutput_wholeTangent]
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [Matrix.cons_val_zero] at firstZero

/-- Complete first source-generated material extension.  Every ordered-pair
output is installed before any semantic consumer reads the expanded packet;
the definition removes only the identically zero wave. -/
def nextMaterialModes : Finset IntegerWavevector :=
  modes ∪ (finiteVorticityPairOutputSupport modes).erase 0

theorem modes_ssubset_nextMaterialModes : modes ⊂ nextMaterialModes := by
  constructor
  · intro wave waveMem
    simp [nextMaterialModes, waveMem]
  · intro reverseSubset
    exact crossScaleOutput_not_mem (reverseSubset (by decide))

theorem crossScaleOutput_mem_nextMaterialModes :
    crossScaleOutput ∈ nextMaterialModes := by
  decide

theorem nextMaterialModes_zero_not_mem :
    (0 : IntegerWavevector) ∉ nextMaterialModes := by
  decide

/-- Finite material face of the actual whole action.  Its coefficients are
computed from the source's full NS tangent; callers cannot submit a row. -/
def actionMaterialState : ComplexVorticityHilbertState :=
  finiteComplexVorticityState nextMaterialModes
    (wholeLatticeVorticityFourierTangentAt
      concreteGrowingViscosity.coeff state)

theorem wholeTangent_supported_on_nextMaterialModes
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ nextMaterialModes) :
    wholeLatticeVorticityFourierTangentAt
        concreteGrowingViscosity.coeff state wave = 0 := by
  by_cases waveZero : wave = 0
  · subst wave
    unfold wholeLatticeVorticityFourierTangentAt
    rw [wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
      state state_transverse, state_zero, smul_zero, sub_zero]
  · have waveNotMemModes : wave ∉ modes := by
      intro waveMem
      apply waveNotMem
      simp [nextMaterialModes, waveMem]
    have waveNotMemOutputs :
        wave ∉ finiteVorticityPairOutputSupport modes := by
      intro outputMem
      apply waveNotMem
      simp [nextMaterialModes, waveZero, outputMem]
    unfold wholeLatticeVorticityFourierTangentAt
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      modes state supported wave]
    rw [finiteStateVorticityNonlinearCoefficientAt_eq_zero_of_not_mem_pairOutput
      modes state wave waveNotMemOutputs]
    rw [supported wave waveNotMemModes, smul_zero, sub_zero]

theorem actionMaterialState_eq_wholeTangent :
    actionMaterialState =
      wholeLatticeVorticityFourierTangentAt
        concreteGrowingViscosity.coeff state := by
  ext wave
  by_cases waveMem : wave ∈ nextMaterialModes
  · rw [actionMaterialState, finiteComplexVorticityState_apply,
      if_pos waveMem]
  · rw [actionMaterialState, finiteComplexVorticityState_apply,
      if_neg waveMem,
      wholeTangent_supported_on_nextMaterialModes wave waveMem]

theorem actionMaterialState_crossScaleOutput :
    actionMaterialState crossScaleOutput = ![-4, -8, 0] := by
  rw [actionMaterialState, finiteComplexVorticityState_apply,
    if_pos crossScaleOutput_mem_nextMaterialModes,
    crossScaleOutput_wholeTangent]

theorem actionMaterialState_crossScaleOutput_ne_zero :
    actionMaterialState crossScaleOutput ≠ 0 := by
  rw [actionMaterialState_crossScaleOutput]
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [Matrix.cons_val_zero] at firstZero

theorem nonlinearWork_eq :
    finiteStateVorticityNonlinearWork modes state = 130 := by
  classical
  unfold finiteStateVorticityNonlinearWork
    finiteStateVorticityNonlinearCoefficientAt
    finiteStateVorticityNonlinearPairContribution
    finiteStateVelocityCoefficient
    biotSavartVelocityCoefficient
  simp (config := { maxSteps := 10000000 })
    [modes, state_p₁, state_q₁, state_r₁, state_l₁,
      state_p₂, state_q₂, state_r₂, state_l₂,
      state_neg_p₁, state_neg_q₁, state_neg_r₁, state_neg_l₁,
      state_neg_p₂, state_neg_q₂, state_neg_r₂, state_neg_l₂,
      waveNeg]
  norm_num [p₁, q₁, r₁, l₁, p₂, q₂, r₂, l₂,
    waveNeg, complexWavevector, integerWaveNormSq, dotProduct,
    cross_apply, complexCoordinateRealInner,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Complex.div_im, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Real.pi_ne_zero, Complex.I_sq]
  field_simp [Real.pi_ne_zero]
  ring

/-! ## Viscosity-dependent source selection on the same two-scale carrier -/

/-- Real amplitude scaling is performed at the primitive source table, so
the resulting state remains a compiled source occurrence rather than a
caller-supplied Hilbert-space vector. -/
def scaledSource (scale : Real) : RawVorticityFourierSource :=
  realScaleRawVorticitySource scale source

def scaledState (scale : Real) : ComplexVorticityHilbertState :=
  generatedComplexVorticityState (scaledSource scale) modes

theorem scaledState_eq_smul (scale : Real) :
    scaledState scale = scale • state := by
  unfold scaledState scaledSource state
  rw [generatedComplexVorticityState_realScale]
  exact (RCLike.real_smul_eq_coe_smul (K := Complex) scale
    (generatedComplexVorticityState source modes)).symm

theorem scaledState_supported
    (scale : Real)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ modes) :
    scaledState scale wave = 0 := by
  rw [scaledState_eq_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, supported wave waveNotMem,
    smul_zero]

theorem scaledState_mass_eq (scale : Real) :
    wholeVorticityEuclideanMass (scaledState scale) =
      scale ^ 2 * 170 := by
  rw [scaledState_eq_smul, wholeVorticityEuclideanMass_real_smul,
    mass_eq]

private theorem complexCoordinateAmplitudeSq_real_smul
    (scale : Real)
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (scale • vector) =
      scale ^ 2 * complexCoordinateAmplitudeSq vector := by
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  change complexCoordinateVectorNormSq ((scale : Complex) • vector) = _
  rw [complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
  ring

theorem scaledState_gradientMass_eq (scale : Real) :
    finiteStateVorticityEnstrophyMass modes (scaledState scale) =
      scale ^ 2 * 910 := by
  rw [scaledState_eq_smul]
  unfold finiteStateVorticityEnstrophyMass
  simp_rw [lp.coeFn_smul, Pi.smul_apply,
    complexCoordinateAmplitudeSq_real_smul]
  calc
    (∑ wave ∈ modes,
        integerWaveNormSq wave *
          (scale ^ 2 * complexCoordinateAmplitudeSq (state wave))) =
        scale ^ 2 * finiteStateVorticityEnstrophyMass modes state := by
      unfold finiteStateVorticityEnstrophyMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _waveMem
      ring
    _ = scale ^ 2 * 910 := by rw [gradientMass_eq]

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
  intro coordinate _coordinateMem
  norm_num
  ring

theorem scaledState_nonlinearWork_eq (scale : Real) :
    finiteStateVorticityNonlinearWork modes (scaledState scale) =
      scale ^ 3 * 130 := by
  have scaledSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → scaledState scale wave = 0 :=
    scaledState_supported scale
  calc
    finiteStateVorticityNonlinearWork modes (scaledState scale) =
        scale ^ 3 * finiteStateVorticityNonlinearWork modes state := by
      unfold finiteStateVorticityNonlinearWork
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [← wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
        modes (scaledState scale) scaledSupported wave]
      rw [scaledState_eq_smul,
        wholeStateVorticityNonlinearCoefficientAt_real_smul]
      rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
        modes state supported wave]
      exact complexCoordinateRealInner_real_smul_cubic scale _ _
    _ = scale ^ 3 * 130 := by rw [nonlinearWork_eq]

/-- Exact source polynomial for the complete half-enstrophy tangent of the
scaled two-scale family. -/
theorem scaledState_generatorWork
    (scale : Real)
    (nu : Viscosity) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner (scaledState scale wave)
        (finiteStateVorticityGenerator modes nu.coeff
          (scaledState scale) wave)) =
      scale ^ 3 * 130 -
        nu.coeff * (2 * Real.pi) ^ 2 * (scale ^ 2 * 910) := by
  rw [finiteStateVorticityGenerator_realWork,
    scaledState_nonlinearWork_eq, scaledState_gradientMass_eq]

/-- Source-selected amplitude making the exact two-scale generator work
strictly positive at every positive viscosity. -/
def regeneratingScale (nu : Viscosity) : Real :=
  14 * (2 * Real.pi) ^ 2 * nu.coeff

theorem regeneratingScale_pos (nu : Viscosity) :
    0 < regeneratingScale nu := by
  unfold regeneratingScale
  exact mul_pos
    (mul_pos (by norm_num) (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
    nu.coeff_pos

def regeneratingSource (nu : Viscosity) : RawVorticityFourierSource :=
  scaledSource (regeneratingScale nu)

def regeneratingState (nu : Viscosity) : ComplexVorticityHilbertState :=
  scaledState (regeneratingScale nu)

theorem regeneratingState_generatorWork
    (nu : Viscosity) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner (regeneratingState nu wave)
        (finiteStateVorticityGenerator modes nu.coeff
          (regeneratingState nu) wave)) =
      (regeneratingScale nu) ^ 2 *
        (910 * (2 * Real.pi) ^ 2 * nu.coeff) := by
  change
    (∑ wave ∈ modes,
      complexCoordinateRealInner (scaledState (regeneratingScale nu) wave)
        (finiteStateVorticityGenerator modes nu.coeff
          (scaledState (regeneratingScale nu)) wave)) = _
  rw [scaledState_generatorWork]
  unfold regeneratingScale
  ring

theorem regeneratingState_generatorWork_pos
    (nu : Viscosity) :
    0 < ∑ wave ∈ modes,
      complexCoordinateRealInner (regeneratingState nu wave)
        (finiteStateVorticityGenerator modes nu.coeff
          (regeneratingState nu) wave) := by
  rw [regeneratingState_generatorWork]
  exact mul_pos (sq_pos_of_pos (regeneratingScale_pos nu))
    (mul_pos
      (mul_pos (by norm_num)
        (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
      nu.coeff_pos)

theorem regeneratingState_zero (nu : Viscosity) :
    regeneratingState nu 0 = 0 := by
  unfold regeneratingState
  rw [scaledState_eq_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, state_zero, smul_zero]

theorem regeneratingState_transverse (nu : Viscosity) :
    WholeStateTransverse (regeneratingState nu) := by
  unfold regeneratingState
  rw [scaledState_eq_smul]
  exact wholeStateTransverse_real_smul _ _ state_transverse

theorem regeneratingState_reality (nu : Viscosity) :
    FiniteStateFourierReality (regeneratingState nu) := by
  intro wave
  unfold regeneratingState
  rw [scaledState_eq_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [state_reality]
  funext coordinate
  simp [vectorConj]

/-- Premise-free viscosity-indexed seed on the full two-scale carrier. -/
def regeneratingSeed (nu : Viscosity) :
    SourceOwnedWholeRestartPhysicalSeed nu where
  physicalState := regeneratingState nu
  physicalState_zero := regeneratingState_zero nu
  transverse := regeneratingState_transverse nu
  reality := regeneratingState_reality nu

def regeneratingReplay (nu : Viscosity) :=
  generatedWholeRestartCanonicalReplay (regeneratingSeed nu)

def regeneratingReceipt (nu : Viscosity) :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    (regeneratingReplay nu)

def regeneratingContact (nu : Viscosity) :=
  generatedPositiveWholeRestartContact (regeneratingReceipt nu)

/-- Actual current whose viscosity, amplitudes, receipt and selected contact
are all generated by the same source occurrence. -/
def regeneratingCurrent (nu : Viscosity) :
    GeneratedWholeRestartCurrent nu where
  initialState := regeneratingState nu
  duration := wholeRestartDuration (regeneratingSeed nu)
  receipt := regeneratingReceipt nu
  contact := regeneratingContact nu

theorem regeneratingReceipt_netPower_zero
    (nu : Viscosity) :
    actualProjectedWholeNetEnstrophyPower
        (regeneratingReceipt nu) modes 0 =
      2 * ((regeneratingScale nu) ^ 2 *
        (910 * (2 * Real.pi) ^ 2 * nu.coeff)) := by
  have sourceReadout :=
    actualProjectedWholeNetEnstrophyPower_zero_eq_generatorRealWork
      (regeneratingReceipt nu) modes
      (scaledState_supported (regeneratingScale nu))
  rw [sourceReadout]
  change 2 *
    (∑ wave ∈ modes,
      complexCoordinateRealInner (regeneratingState nu wave)
        (finiteStateVorticityGenerator modes nu.coeff
          (regeneratingState nu) wave)) = _
  rw [regeneratingState_generatorWork]

theorem regeneratingReceipt_netPower_zero_pos
    (nu : Viscosity) :
    0 < actualProjectedWholeNetEnstrophyPower
      (regeneratingReceipt nu) modes 0 := by
  rw [regeneratingReceipt_netPower_zero]
  have workPos := regeneratingState_generatorWork_pos nu
  rw [regeneratingState_generatorWork] at workPos
  exact mul_pos (by norm_num) workPos

/-- Half of the exact time-zero net power.  This is computed from the source
polynomial and is not supplied by a continuation consumer. -/
def regeneratingNetPowerThreshold (nu : Viscosity) : Real :=
  (regeneratingScale nu) ^ 2 *
    (910 * (2 * Real.pi) ^ 2 * nu.coeff)

theorem regeneratingNetPowerThreshold_pos (nu : Viscosity) :
    0 < regeneratingNetPowerThreshold nu := by
  unfold regeneratingNetPowerThreshold
  have workPos := regeneratingState_generatorWork_pos nu
  rw [regeneratingState_generatorWork] at workPos
  exact workPos

/-- The exact source power generates its own local patch around time zero. -/
theorem regeneratingReceipt_netPower_initial_patch
    (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Set.Icc (0 : Real)
          (wholeRestartDuration (regeneratingSeed nu)),
        actual < epsilon →
          regeneratingNetPowerThreshold nu <
            actualProjectedWholeNetEnstrophyPower
              (regeneratingReceipt nu) modes actual := by
  let netPower : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower
      (regeneratingReceipt nu) modes actual
  have netPowerContinuous : Continuous netPower :=
    actualProjectedWholeNetEnstrophyPower_continuous
      (regeneratingReceipt nu) modes
  have zeroMem : 0 ∈
      {actual | regeneratingNetPowerThreshold nu < netPower actual} := by
    change regeneratingNetPowerThreshold nu <
      actualProjectedWholeNetEnstrophyPower
        (regeneratingReceipt nu) modes 0
    rw [regeneratingReceipt_netPower_zero]
    change regeneratingNetPowerThreshold nu <
      2 * regeneratingNetPowerThreshold nu
    linarith [regeneratingNetPowerThreshold_pos nu]
  have neighborhoodOpen :
      IsOpen {actual |
        regeneratingNetPowerThreshold nu < netPower actual} :=
    isOpen_lt continuous_const netPowerContinuous
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

noncomputable def regeneratingNetPowerPatchTime
    (nu : Viscosity) : Real :=
  Classical.choose (regeneratingReceipt_netPower_initial_patch nu)

theorem regeneratingNetPowerPatchTime_pos (nu : Viscosity) :
    0 < regeneratingNetPowerPatchTime nu :=
  (Classical.choose_spec
    (regeneratingReceipt_netPower_initial_patch nu)).1

theorem regeneratingNetPowerPatchTime_spec
    (nu : Viscosity)
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration (regeneratingSeed nu)))
    (actualLt : actual < regeneratingNetPowerPatchTime nu) :
    regeneratingNetPowerThreshold nu <
      actualProjectedWholeNetEnstrophyPower
        (regeneratingReceipt nu) modes actual :=
  (Classical.choose_spec
    (regeneratingReceipt_netPower_initial_patch nu)).2
      actual actualMem actualLt

/-- Source-owned initial patch duration.  The public current contains the
resulting receipt and contact, not this local continuity witness. -/
def regeneratingShortDuration (nu : Viscosity) : Real :=
  min (wholeRestartDuration (regeneratingSeed nu))
      (regeneratingNetPowerPatchTime nu) / 2

theorem regeneratingShortDuration_pos (nu : Viscosity) :
    0 < regeneratingShortDuration nu := by
  unfold regeneratingShortDuration
  exact div_pos
    (lt_min (wholeRestartDuration_pos (regeneratingSeed nu))
      (regeneratingNetPowerPatchTime_pos nu))
    (by norm_num)

theorem regeneratingShortDuration_le_original (nu : Viscosity) :
    regeneratingShortDuration nu ≤
      wholeRestartDuration (regeneratingSeed nu) := by
  unfold regeneratingShortDuration
  have minLe := min_le_left
    (wholeRestartDuration (regeneratingSeed nu))
    (regeneratingNetPowerPatchTime nu)
  have minPos : 0 < min
      (wholeRestartDuration (regeneratingSeed nu))
      (regeneratingNetPowerPatchTime nu) :=
    lt_min (wholeRestartDuration_pos (regeneratingSeed nu))
      (regeneratingNetPowerPatchTime_pos nu)
  nlinarith

theorem regeneratingShortDuration_lt_patch (nu : Viscosity) :
    regeneratingShortDuration nu <
      regeneratingNetPowerPatchTime nu := by
  unfold regeneratingShortDuration
  have minLe := min_le_right
    (wholeRestartDuration (regeneratingSeed nu))
    (regeneratingNetPowerPatchTime nu)
  nlinarith [regeneratingNetPowerPatchTime_pos nu]

def regeneratingShortReceipt (nu : Viscosity) :
    WholeContinuousMildSerrinReceipt nu (regeneratingState nu)
      (regeneratingShortDuration nu) :=
  restrictWholeContinuousMildSerrinReceipt
    (regeneratingShortDuration_pos nu)
    (regeneratingShortDuration_le_original nu)
    (regeneratingReceipt nu)

def regeneratingShortContact (nu : Viscosity) :=
  generatedPositiveWholeRestartContact (regeneratingShortReceipt nu)

/-- Current whose stage-zero contact still carries the source-selected
positive action instruction. -/
def regeneratingShortCurrent (nu : Viscosity) :
    GeneratedWholeRestartCurrent nu where
  initialState := regeneratingState nu
  duration := regeneratingShortDuration nu
  receipt := regeneratingShortReceipt nu
  contact := regeneratingShortContact nu

/-- Every time in the selected initial contact prefix still carries the
source-generated positive action instruction. -/
theorem regeneratingShortContact_prefix_netPower_gt_threshold
    (nu : Viscosity)
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      (regeneratingShortContact nu).time.1) :
    regeneratingNetPowerThreshold nu <
      actualProjectedWholeNetEnstrophyPower
        (regeneratingShortContact nu).prefixReceipt modes actual := by
  have actualLeShort : actual ≤ regeneratingShortDuration nu :=
    actualMem.2.trans (regeneratingShortContact nu).time.2.2
  have actualMemOriginal : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration (regeneratingSeed nu)) :=
    ⟨actualMem.1,
      actualLeShort.trans (regeneratingShortDuration_le_original nu)⟩
  have actualLtPatch : actual < regeneratingNetPowerPatchTime nu :=
    actualLeShort.trans_lt (regeneratingShortDuration_lt_patch nu)
  have stateEq :
      (actualWholeProjectedTransversePath
        (regeneratingShortContact nu).prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath
        (regeneratingReceipt nu) actual).1 := by
    change (regeneratingShortContact nu).prefixReceipt.wholePath
        (Set.projIcc (0 : Real)
          (regeneratingShortContact nu).time.1
          (regeneratingShortContact nu).time_pos.le actual) =
      (regeneratingReceipt nu).wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration (regeneratingSeed nu))
          (regeneratingReceipt nu).requestedTimePos.le actual)
    rw [Set.projIcc_of_mem
      (regeneratingShortContact nu).time_pos.le actualMem]
    rw [Set.projIcc_of_mem
      (regeneratingReceipt nu).requestedTimePos.le actualMemOriginal]
    rfl
  have sourcePositive := regeneratingNetPowerPatchTime_spec
    nu actual actualMemOriginal actualLtPatch
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [stateEq]
  exact sourcePositive

/-- The positive instruction is now attached to the exact stage-zero
contact: it is the time-zero row of that contact's generated next receipt. -/
theorem regeneratingShortCurrent_nextReceipt_netPower_zero_gt_threshold
    (nu : Viscosity) :
    regeneratingNetPowerThreshold nu <
      actualProjectedWholeNetEnstrophyPower
        (regeneratingShortCurrent nu).nextReceipt modes 0 := by
  have terminalPositive :=
    regeneratingShortContact_prefix_netPower_gt_threshold nu
      (regeneratingShortContact nu).time.1
      ⟨(regeneratingShortContact nu).time_pos.le, le_rfl⟩
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          (regeneratingShortCurrent nu).nextReceipt modes 0 =
        actualProjectedWholeNetEnstrophyPower
          (regeneratingShortContact nu).prefixReceipt modes
          (regeneratingShortContact nu).time.1 := by
    simpa only [regeneratingShortCurrent] using
      nextReceipt_netPower_zero_eq_contact_selectedEndpoint
        (regeneratingShortCurrent nu) modes
  rwa [powerEq]

/-- Strong same-viscosity candidate for the final public source selection.
It remains distinct from the legacy outflux current until its generated
cell-failure face is eliminated. -/
def concreteTwoScaleRegeneratingInitial :
    GeneratedWholeRestartCurrent concreteCounterexampleViscosity :=
  regeneratingShortCurrent concreteCounterexampleViscosity

theorem concreteTwoScaleRegeneratingInitial_netPower_zero_pos :
    regeneratingNetPowerThreshold concreteCounterexampleViscosity <
      actualProjectedWholeNetEnstrophyPower
        concreteTwoScaleRegeneratingInitial.nextReceipt modes 0 := by
  exact regeneratingShortCurrent_nextReceipt_netPower_zero_gt_threshold
    concreteCounterexampleViscosity

theorem generatorWork_concreteGrowingViscosity_eq :
    (∑ wave ∈ modes,
      complexCoordinateRealInner (state wave)
        (finiteStateVorticityGenerator modes
          concreteGrowingViscosity.coeff state wave)) = 65 := by
  rw [finiteStateVorticityGenerator_realWork,
    nonlinearWork_eq, gradientMass_eq]
  unfold concreteGrowingViscosity
  field_simp [Real.pi_ne_zero]
  ring

theorem generatorWork_concreteGrowingViscosity_pos :
    0 <
      ∑ wave ∈ modes,
        complexCoordinateRealInner (state wave)
          (finiteStateVorticityGenerator modes
            concreteGrowingViscosity.coeff state wave) := by
  rw [generatorWork_concreteGrowingViscosity_eq]
  norm_num

def physicalSeed :
    SourceOwnedWholeRestartPhysicalSeed concreteGrowingViscosity where
  physicalState := state
  physicalState_zero := state_zero
  transverse := state_transverse
  reality := state_reality

theorem physicalSeed_crossScaleOutput_wholeTangent :
    wholeLatticeVorticityFourierTangentAt
        concreteGrowingViscosity.coeff
        (wholeRestartPhysicalState physicalSeed) crossScaleOutput =
      ![-4, -8, 0] := by
  exact crossScaleOutput_wholeTangent

def replay := generatedWholeRestartCanonicalReplay physicalSeed

def receipt :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt replay

theorem receipt_crossScaleRow_hasDerivAt_zero :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath receipt crossScaleOutput)
      ![-4, -8, 0] 0 := by
  simpa only [wholeLatticeVorticityFourierTangentAt] using
    (actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      receipt crossScaleOutput).congr_deriv crossScaleOutput_wholeTangent

theorem receipt_highScaleRow_hasDerivAt_zero :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath receipt highScaleOutput)
      ![32, -16, 0] 0 := by
  simpa only [wholeLatticeVorticityFourierTangentAt] using
    (actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      receipt highScaleOutput).congr_deriv highScaleOutput_wholeTangent

theorem crossScaleTangent_ne_zero :
    (![-4, -8, 0] : ComplexCoordinateVector) ≠ 0 := by
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [Matrix.cons_val_zero] at firstZero

theorem exists_crossScaleRowPersistenceTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath
          receipt crossScaleOutput actual ≠ 0 := by
  have punctured :=
    receipt_crossScaleRow_hasDerivAt_zero.eventually_ne
      crossScaleTangent_ne_zero (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in 𝓝 (0 : Real),
        actual ≠ 0 →
          actualWholeContinuousHeatDuhamelPath
            receipt crossScaleOutput actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

noncomputable def crossScaleRowPersistenceTime : Real :=
  Classical.choose exists_crossScaleRowPersistenceTime

theorem crossScaleRowPersistenceTime_pos :
    0 < crossScaleRowPersistenceTime :=
  (Classical.choose_spec exists_crossScaleRowPersistenceTime).1

theorem crossScaleRowPersistenceTime_spec
    (actual : Real)
    (actualPos : 0 < actual)
    (actualLt : actual < crossScaleRowPersistenceTime) :
    actualWholeContinuousHeatDuhamelPath
      receipt crossScaleOutput actual ≠ 0 :=
  (Classical.choose_spec exists_crossScaleRowPersistenceTime).2
    actual actualPos actualLt

theorem highScaleTangentRow_ne_zero :
    (![32, -16, 0] : ComplexCoordinateVector) ≠ 0 := by
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [Matrix.cons_val_zero] at firstZero

theorem exists_highScaleRowPersistenceTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath
          receipt highScaleOutput actual ≠ 0 := by
  have punctured :=
    receipt_highScaleRow_hasDerivAt_zero.eventually_ne
      highScaleTangentRow_ne_zero (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in 𝓝 (0 : Real),
        actual ≠ 0 →
          actualWholeContinuousHeatDuhamelPath
            receipt highScaleOutput actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

noncomputable def highScaleRowPersistenceTime : Real :=
  Classical.choose exists_highScaleRowPersistenceTime

theorem highScaleRowPersistenceTime_pos :
    0 < highScaleRowPersistenceTime :=
  (Classical.choose_spec exists_highScaleRowPersistenceTime).1

theorem highScaleRowPersistenceTime_spec
    (actual : Real)
    (actualPos : 0 < actual)
    (actualLt : actual < highScaleRowPersistenceTime) :
    actualWholeContinuousHeatDuhamelPath
      receipt highScaleOutput actual ≠ 0 :=
  (Classical.choose_spec exists_highScaleRowPersistenceTime).2
    actual actualPos actualLt

def materialDuration : Real :=
  min
      (min (wholeRestartDuration physicalSeed)
        crossScaleRowPersistenceTime)
      highScaleRowPersistenceTime / 2

theorem materialDuration_pos : 0 < materialDuration := by
  unfold materialDuration
  exact div_pos
    (lt_min
      (lt_min (wholeRestartDuration_pos physicalSeed)
        crossScaleRowPersistenceTime_pos)
      highScaleRowPersistenceTime_pos)
    (by norm_num)

theorem materialDuration_le_original :
    materialDuration ≤ wholeRestartDuration physicalSeed := by
  unfold materialDuration
  have outerLe := min_le_left
    (min (wholeRestartDuration physicalSeed)
      crossScaleRowPersistenceTime)
    highScaleRowPersistenceTime
  have innerLe := min_le_left
    (wholeRestartDuration physicalSeed) crossScaleRowPersistenceTime
  have outerPos :
      0 < min
        (min (wholeRestartDuration physicalSeed)
          crossScaleRowPersistenceTime)
        highScaleRowPersistenceTime :=
    lt_min
      (lt_min (wholeRestartDuration_pos physicalSeed)
        crossScaleRowPersistenceTime_pos)
      highScaleRowPersistenceTime_pos
  nlinarith

theorem materialDuration_lt_persistence :
    materialDuration < crossScaleRowPersistenceTime := by
  unfold materialDuration
  have outerLe := min_le_left
    (min (wholeRestartDuration physicalSeed)
      crossScaleRowPersistenceTime)
    highScaleRowPersistenceTime
  have innerLe := min_le_right
    (wholeRestartDuration physicalSeed) crossScaleRowPersistenceTime
  nlinarith [crossScaleRowPersistenceTime_pos]

theorem materialDuration_lt_highScalePersistence :
    materialDuration < highScaleRowPersistenceTime := by
  unfold materialDuration
  have minLe := min_le_right
    (min (wholeRestartDuration physicalSeed)
      crossScaleRowPersistenceTime)
    highScaleRowPersistenceTime
  nlinarith [highScaleRowPersistenceTime_pos]

def materialReceipt :
    WholeContinuousMildSerrinReceipt
      concreteGrowingViscosity state materialDuration :=
  restrictWholeContinuousMildSerrinReceipt
    materialDuration_pos materialDuration_le_original receipt

def materialContact := generatedPositiveWholeRestartContact materialReceipt

def materialCurrent :
    GeneratedWholeRestartCurrent concreteGrowingViscosity where
  initialState := state
  duration := materialDuration
  receipt := materialReceipt
  contact := materialContact

def materialContactOriginalTime :
    Set.Icc (0 : Real) (wholeRestartDuration physicalSeed) :=
  commonTimeInclusion materialDuration_le_original materialContact.time

theorem materialContactOriginalTime_pos :
    0 < materialContactOriginalTime.1 :=
  materialContact.time_pos

theorem materialContactOriginalTime_lt_persistence :
    materialContactOriginalTime.1 < crossScaleRowPersistenceTime :=
  lt_of_le_of_lt materialContact.time.2.2 materialDuration_lt_persistence

theorem materialContactOriginalTime_lt_highScalePersistence :
    materialContactOriginalTime.1 < highScaleRowPersistenceTime :=
  lt_of_le_of_lt materialContact.time.2.2
    materialDuration_lt_highScalePersistence

theorem materialContact_crossScaleRow_ne_zero :
    materialContact.physicalState crossScaleOutput ≠ 0 := by
  change receipt.wholePath materialContactOriginalTime crossScaleOutput ≠ 0
  rw [wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    receipt crossScaleOutput (by decide) materialContactOriginalTime]
  exact crossScaleRowPersistenceTime_spec
    materialContactOriginalTime.1
    materialContactOriginalTime_pos
    materialContactOriginalTime_lt_persistence

theorem materialContact_highScaleRow_ne_zero :
    materialContact.physicalState highScaleOutput ≠ 0 := by
  change receipt.wholePath materialContactOriginalTime highScaleOutput ≠ 0
  rw [wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    receipt highScaleOutput (by decide) materialContactOriginalTime]
  exact highScaleRowPersistenceTime_spec
    materialContactOriginalTime.1
    materialContactOriginalTime_pos
    materialContactOriginalTime_lt_highScalePersistence

theorem materialContact_generates_strict_support_extension :
    ∃ wave : IntegerWavevector,
      wave ∈ nextMaterialModes ∧ wave ∉ modes ∧
        materialContact.physicalState wave ≠ 0 := by
  exact ⟨crossScaleOutput,
    crossScaleOutput_mem_nextMaterialModes,
    crossScaleOutput_not_mem,
    materialContact_crossScaleRow_ne_zero⟩

theorem materialContact_not_supported_on_originalModes :
    ¬ (∀ wave : IntegerWavevector,
      wave ∉ modes → materialContact.physicalState wave = 0) := by
  intro oldSupport
  exact materialContact_crossScaleRow_ne_zero
    (oldSupport crossScaleOutput crossScaleOutput_not_mem)

/-! ## Same-occurrence oriented subcell transfer -/

/-- Kinetic valuation of the explicit reality-paired receiver row generated
by the actual material contact. -/
def materialReceiverKineticCredit : Real :=
  complexCoordinateAmplitudeSq
      (materialContact.physicalState highScaleOutput) /
    integerWaveViscousMultiplier highScaleOutput

/-- Kinetic mass still carried by the original finite donor inventory at the
same actual endpoint. -/
def materialRetainedOriginalKinetic : Real :=
  puncturedWholeVorticityKineticMass
    (complexSharpSupportProjection modes materialContact.physicalState)

/-- Complete kinetic complement outside the original donor inventory. -/
def materialFreshKineticCredit : Real :=
  puncturedWholeVorticityKineticMass materialContact.physicalState -
    materialRetainedOriginalKinetic

/-- Kinetic debit of the original donor inventory, measured against its
source state on this exact occurrence. -/
def materialDonorKineticDebit : Real :=
  puncturedWholeVorticityKineticMass state -
    materialRetainedOriginalKinetic

/-- Viscous payment on the same original receipt prefix which generated the
material contact. -/
def materialSubcellViscousPayment : Real :=
  2 * concreteGrowingViscosity.coeff *
    wholePrefixVorticityMass materialContactOriginalTime receipt.stateLimit

theorem materialReceiverKineticCredit_pos :
    0 < materialReceiverKineticCredit := by
  unfold materialReceiverKineticCredit
  apply div_pos
  · rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    exact (complexCoordinateVectorNormSq_pos_iff _).2
      materialContact_highScaleRow_ne_zero
  · unfold integerWaveViscousMultiplier
    exact mul_pos (sq_pos_of_pos (by positivity))
      (by
        exact_mod_cast
          (integerWaveNormSq_pos
            (show highScaleOutput ≠ 0 by decide)))

theorem materialRetained_add_receiver_le_whole :
    materialRetainedOriginalKinetic + materialReceiverKineticCredit ≤
      puncturedWholeVorticityKineticMass materialContact.physicalState := by
  let extendedModes := insert highScaleOutput modes
  have extendedZeroNotMem : (0 : IntegerWavevector) ∉ extendedModes := by
    dsimp only [extendedModes]
    simp only [Finset.mem_insert, not_or]
    exact
      ⟨by decide,
        by rw [← source_support_eq_modes]; exact zero_not_mem⟩
  have projectionLe :=
    puncturedWholeVorticityKineticMass_sharpSupportProjection_le
      extendedModes extendedZeroNotMem materialContact.physicalState
  have extendedEq :
      puncturedWholeVorticityKineticMass
          (complexSharpSupportProjection extendedModes
            materialContact.physicalState) =
        materialRetainedOriginalKinetic +
          materialReceiverKineticCredit := by
    unfold materialRetainedOriginalKinetic materialReceiverKineticCredit
    rw [puncturedWholeVorticityKineticMass_eq_finite_of_supported
      extendedModes extendedZeroNotMem
      (complexSharpSupportProjection extendedModes
        materialContact.physicalState)
      (by
        intro wave waveNotMem
        simp [complexSharpSupportProjection_apply, waveNotMem])]
    rw [puncturedWholeVorticityKineticMass_eq_finite_of_supported
      modes (by rw [← source_support_eq_modes]; exact zero_not_mem)
      (complexSharpSupportProjection modes materialContact.physicalState)
      (by
        intro wave waveNotMem
        simp [complexSharpSupportProjection_apply, waveNotMem])]
    rw [Finset.sum_insert highScaleOutput_not_mem]
    simp only [extendedModes, complexSharpSupportProjection_apply,
      Finset.mem_insert, true_or, if_true]
    nth_rewrite 1 [add_comm]
    apply congrArg₂ (· + ·) ?_ rfl
    apply Finset.sum_congr rfl
    intro wave waveMem
    simp only [waveMem, or_true, if_true]
  rw [extendedEq] at projectionLe
  exact projectionLe

theorem materialFreshKineticCredit_pos :
    0 < materialFreshKineticCredit := by
  have receiverPos := materialReceiverKineticCredit_pos
  have receiverLe := materialRetained_add_receiver_le_whole
  unfold materialFreshKineticCredit
  linarith

theorem materialContact_physicalState_eq_originalReceipt :
    receipt.wholePath materialContactOriginalTime =
      materialContact.physicalState := by
  change receipt.wholePath materialContactOriginalTime =
    materialReceipt.wholePath materialContact.time
  rfl

theorem physicalSeed_physicalState_eq_state :
    wholeRestartPhysicalState physicalSeed = state := by
  simp only [wholeRestartPhysicalState]
  rfl

/-- Exact donor/receiver/viscosity balance on the actual generated contact.
This is the quantitative valuation of the same fresh-row incidence; no
support cardinality or synthetic receiver state enters the equality. -/
theorem materialDonorKineticDebit_eq_freshCredit_add_viscousPayment :
    materialDonorKineticDebit =
      materialFreshKineticCredit + materialSubcellViscousPayment := by
  have ledger :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_eq
      replay materialContactOriginalTime
  change
    puncturedWholeVorticityKineticMass
          (receipt.wholePath materialContactOriginalTime) +
        2 * concreteGrowingViscosity.coeff *
          wholePrefixVorticityMass materialContactOriginalTime
            receipt.stateLimit =
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState physicalSeed) at ledger
  rw [materialContact_physicalState_eq_originalReceipt] at ledger
  have sourceKineticEq :
      puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState physicalSeed) =
        puncturedWholeVorticityKineticMass state :=
    congrArg puncturedWholeVorticityKineticMass
      physicalSeed_physicalState_eq_state
  unfold materialDonorKineticDebit materialFreshKineticCredit
    materialSubcellViscousPayment
  linarith [sourceKineticEq]

theorem materialDonorKineticDebit_pos :
    0 < materialDonorKineticDebit := by
  rw [materialDonorKineticDebit_eq_freshCredit_add_viscousPayment]
  exact add_pos_of_pos_of_nonneg materialFreshKineticCredit_pos
    (mul_nonneg
      (mul_nonneg (by norm_num) concreteGrowingViscosity.coeff_pos.le)
      (wholePrefixVorticityMass_nonneg
        materialContactOriginalTime receipt.stateLimit))

/-- Direct source-only subcell producer on the concrete actual occurrence. -/
theorem materialContact_nativeSubcellTransfer :
    0 < materialReceiverKineticCredit ∧
      0 < materialFreshKineticCredit ∧
      materialDonorKineticDebit =
        materialFreshKineticCredit + materialSubcellViscousPayment ∧
      0 < materialDonorKineticDebit :=
  ⟨materialReceiverKineticCredit_pos,
    materialFreshKineticCredit_pos,
    materialDonorKineticDebit_eq_freshCredit_add_viscousPayment,
    materialDonorKineticDebit_pos⟩

theorem crossScaleOutput_mem_sourceGeneratedRunKernelInventory
    (initial : GeneratedWholeRestartCurrent concreteGrowingViscosity)
    (stage : Nat) :
    crossScaleOutput ∈ sourceGeneratedRunKernelInventory initial stage := by
  have radiusLe :
      integerWaveCoordinateRadius crossScaleOutput ≤
        sourceOwnedLocalKernelRadius concreteGrowingViscosity
          (restartCoefficientCeiling initial stage) := by
    rw [show integerWaveCoordinateRadius crossScaleOutput = 2 by decide]
    exact sourceOwnedLocalKernelRadius_two_le _ _
  have coreMem : crossScaleOutput ∈
      sourceOwnedLocalKernelCore concreteGrowingViscosity
        (restartCoefficientCeiling initial stage) := by
    rw [sourceOwnedLocalKernelCore_eq_frequencyCube]
    exact integerWave_mem_frequencyCube_of_radius_le
      crossScaleOutput _ radiusLe
  exact sourceGeneratedRunKernelCore_subset_inventory initial stage
    (Finset.mem_erase.mpr ⟨by decide, coreMem⟩)

theorem receipt_netPower_zero_eq :
    actualProjectedWholeNetEnstrophyPower receipt modes 0 = 130 := by
  have sourceReadout :=
    actualProjectedWholeNetEnstrophyPower_zero_eq_generatorRealWork
      receipt modes supported
  rw [sourceReadout]
  change 2 *
    (∑ wave ∈ modes,
      complexCoordinateRealInner (state wave)
        (finiteStateVorticityGenerator modes
          concreteGrowingViscosity.coeff state wave)) = 130
  rw [generatorWork_concreteGrowingViscosity_eq]
  norm_num

theorem receipt_netPower_zero_pos :
    0 < actualProjectedWholeNetEnstrophyPower receipt modes 0 := by
  rw [receipt_netPower_zero_eq]
  norm_num

end
end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteTwoScaleLiftSource
end NavierStokes
end SaturationMonoid
