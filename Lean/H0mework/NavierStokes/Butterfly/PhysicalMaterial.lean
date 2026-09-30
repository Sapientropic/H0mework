import H0mework.NavierStokes.Butterfly.SubcellRecurrence
import H0mework.NavierStokes.KineticRestart.ExactKineticDissipation
import H0mework.NavierStokes.Fourier.CanonicalExhaustiveGalerkinTarget
import H0mework.NavierStokes.Restart.NativeRecursion

/-!
# Source-generated physical butterfly material

The finite two-pump rational carrier is promoted to a transverse, reality-closed
whole-vorticity seed. Its complete first doubled-axis fibre is the actual whole
NS tangent, and the source receipt generates a positive-time contact on which
that fresh higher-frequency row is nonzero.

This file supplies one local physical material edge. It does not identify the
selected endpoint with a precomputed next template or store a future contact
sequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000

open scoped Matrix BigOperators Topology

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator

open Matrix Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart

noncomputable section

def butterflyPhysicalState (a : ℚ) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState butterflySeedModes fun wave =>
    GaussianRatVector.toComplex (butterflySeedRow a wave)

theorem butterflyPhysicalState_apply
    (a : ℚ) (wave : IntegerWavevector) :
    butterflyPhysicalState a wave =
      if wave ∈ butterflySeedModes then
        GaussianRatVector.toComplex (butterflySeedRow a wave)
      else 0 := by
  rw [butterflyPhysicalState, finiteComplexVorticityState_apply]

theorem butterflySeedModes_zero_not_mem :
    (0 : IntegerWavevector) ∉ butterflySeedModes := by decide

theorem butterflyPhysicalState_zero (a : ℚ) :
    butterflyPhysicalState a 0 = 0 := by
  rw [butterflyPhysicalState_apply, if_neg butterflySeedModes_zero_not_mem]

theorem butterflyPhysicalState_supported
    (a : ℚ) (wave : IntegerWavevector)
    (waveNotMem : wave ∉ butterflySeedModes) :
    butterflyPhysicalState a wave = 0 := by
  rw [butterflyPhysicalState_apply, if_neg waveNotMem]

theorem butterflySeedRow_waveDot_zero
    (a : ℚ) (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflySeedModes) :
    GaussianRatVector.waveDot wave (butterflySeedRow a wave) = 0 := by
  simp only [butterflySeedModes, butterflyZTwoModes,
    Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl
  all_goals
    apply GaussianRat.ext <;>
    simp [butterflySeedRow, butterflyZTwoRow,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      axisWave, pumpY, pumpZ, realRow, realGaussian,
      GaussianRatVector.waveDot, GaussianRat.add,
      GaussianRat.ratScale, GaussianRat.intScale,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    ring

theorem butterflyPhysicalState_transverse (a : ℚ) :
    WholeStateTransverse (butterflyPhysicalState a) := by
  intro wave
  by_cases waveMem : wave ∈ butterflySeedModes
  · rw [butterflyPhysicalState_apply, if_pos waveMem]
    rw [← GaussianRatVector.toComplex_waveDot]
    rw [butterflySeedRow_waveDot_zero a wave waveMem]
    exact GaussianRat.toComplex_zero
  · rw [butterflyPhysicalState_supported a wave waveMem, dotProduct_zero]

theorem butterflySeedRow_neg_eq
    (a : ℚ) (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflySeedModes) :
    butterflySeedRow a (waveNeg wave) = butterflySeedRow a wave := by
  simp only [butterflySeedModes, butterflyZTwoModes,
    Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl
  all_goals
    funext coordinate
    fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [butterflySeedRow, butterflyZTwoRow,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      axisWave, pumpY, pumpZ, waveNeg, realRow, realGaussian,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

theorem butterflySeedModes_waveNeg_mem
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflySeedModes) :
    waveNeg wave ∈ butterflySeedModes := by
  simp only [butterflySeedModes, butterflyZTwoModes,
      Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at waveMem ⊢
  rcases waveMem with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl
  all_goals simp [axisWave, pumpY, pumpZ, waveNeg]

theorem butterflySeedModes_waveNeg_mem_iff (wave : IntegerWavevector) :
    waveNeg wave ∈ butterflySeedModes ↔
      wave ∈ butterflySeedModes := by
  constructor
  · intro negMem
    have := butterflySeedModes_waveNeg_mem (waveNeg wave) negMem
    simpa using this
  · exact butterflySeedModes_waveNeg_mem wave

theorem butterflySeedRow_im_zero
    (a : ℚ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    (butterflySeedRow a wave coordinate).im = 0 := by
  unfold butterflySeedRow butterflyZTwoRow
  split_ifs <;> fin_cases coordinate <;>
    simp [sidebandPlusZ_eq, sidebandMinusZ_eq, realRow, realGaussian]

theorem butterflyPhysicalState_reality (a : ℚ) :
    FiniteStateFourierReality (butterflyPhysicalState a) := by
  intro wave
  by_cases waveMem : wave ∈ butterflySeedModes
  · have negMem := (butterflySeedModes_waveNeg_mem_iff wave).2 waveMem
    rw [butterflyPhysicalState_apply, if_pos negMem,
      butterflyPhysicalState_apply, if_pos waveMem,
      butterflySeedRow_neg_eq a wave waveMem]
    funext coordinate
    change GaussianRat.toComplex (butterflySeedRow a wave coordinate) =
      star (GaussianRat.toComplex (butterflySeedRow a wave coordinate))
    unfold GaussianRat.toComplex
    rw [butterflySeedRow_im_zero a wave coordinate]
    simp
  · have negNotMem : waveNeg wave ∉ butterflySeedModes := by
      intro negMem
      exact waveMem ((butterflySeedModes_waveNeg_mem_iff wave).1 negMem)
    rw [butterflyPhysicalState_apply, if_neg negNotMem,
      butterflyPhysicalState_apply, if_neg waveMem]
    exact ThreeDimensionalVorticityCoefficientRawSourceCore.vectorConj_zero.symm

theorem butterflyZTwoTarget_not_mem :
    axisWave 4 ∉ butterflySeedModes := by decide

private theorem finiteNonlinear_eq_single_sum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityNonlinearCoefficientAt modes state output =
      ∑ first ∈ modes,
        if output - first ∈ modes then
          finiteStateVorticityNonlinearPairContribution
            state (first, output - first)
        else 0 := by
  unfold finiteStateVorticityNonlinearCoefficientAt
  apply Finset.sum_congr rfl
  intro first firstMem
  have condition : ∀ second : IntegerWavevector,
      first + second = output ↔ second = output - first := by
    intro second
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [condition]
  by_cases secondMem : output - first ∈ modes
  · simp [secondMem]
  · simp [secondMem]

theorem butterflyPhysicalState_finiteNonlinear_target (a : ℚ) :
    finiteStateVorticityNonlinearCoefficientAt
        butterflySeedModes (butterflyPhysicalState a) (axisWave 4) =
      GaussianRatVector.toComplex (butterflySeedFullFibre a) := by
  rw [finiteNonlinear_eq_single_sum]
  rw [butterflySeedFullFibre,
    GaussianRatVector.toComplex_finsetSum]
  apply Finset.sum_congr rfl
  intro first firstMem
  let second := axisWave 4 - first
  by_cases secondMem : second ∈ butterflySeedModes
  · rw [if_pos secondMem, if_pos secondMem]
    symm
    apply rationalVorticityPairContribution_toComplex_self
      (butterflyPhysicalState a)
    · exact fun firstZero =>
        butterflySeedModes_zero_not_mem (firstZero ▸ firstMem)
    · exact fun secondZero =>
        butterflySeedModes_zero_not_mem (secondZero ▸ secondMem)
    · exact (butterflyPhysicalState_apply a first).trans
        (if_pos firstMem) |>.symm
    · exact (butterflyPhysicalState_apply a second).trans
        (if_pos secondMem) |>.symm
  · rw [if_neg secondMem, if_neg secondMem]
    exact GaussianRatVector.toComplex_zero_instance.symm

theorem butterflyPhysicalState_wholeNonlinear_target (a : ℚ) :
    wholeStateVorticityNonlinearCoefficientAt
        (butterflyPhysicalState a) (axisWave 4) =
      GaussianRatVector.toComplex (butterflySeedFullFibre a) := by
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState a)
    (butterflyPhysicalState_supported a) (axisWave 4)]
  exact butterflyPhysicalState_finiteNonlinear_target a

theorem butterflyPhysicalState_target_zero (a : ℚ) :
    butterflyPhysicalState a (axisWave 4) = 0 :=
  butterflyPhysicalState_supported a (axisWave 4)
    butterflyZTwoTarget_not_mem

theorem butterflyPhysicalState_wholeTangent_target
    (nu : Viscosity) (a : ℚ) :
    wholeLatticeVorticityFourierTangentAt nu.coeff
        (butterflyPhysicalState a) (axisWave 4) =
      GaussianRatVector.toComplex (butterflySeedFullFibre a) := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [butterflyPhysicalState_wholeNonlinear_target,
    butterflyPhysicalState_target_zero, smul_zero, sub_zero]

theorem butterflyPhysicalState_wholeTangent_target_ne_zero
    (nu : Viscosity) {a : ℚ} (aNe : a ≠ 0) :
    wholeLatticeVorticityFourierTangentAt nu.coeff
        (butterflyPhysicalState a) (axisWave 4) ≠ 0 := by
  rw [butterflyPhysicalState_wholeTangent_target,
    butterflySeedFullFibre_eq, butterflyZTwoFullFibre_eq]
  intro rowZero
  have targetZero := congrFun rowZero 2
  simp [realRow, realGaussian, GaussianRatVector.toComplex,
    GaussianRat.toComplex] at targetZero
  exact aNe targetZero

def butterflyPhysicalSeed (nu : Viscosity) :
    SourceOwnedWholeRestartPhysicalSeed nu where
  physicalState := butterflyPhysicalState 1
  physicalState_zero := butterflyPhysicalState_zero 1
  transverse := butterflyPhysicalState_transverse 1
  reality := butterflyPhysicalState_reality 1

@[simp] theorem butterflyPhysicalSeed_wholeState (nu : Viscosity) :
    wholeRestartPhysicalState (butterflyPhysicalSeed nu) =
      butterflyPhysicalState 1 := rfl

def butterflyReplay (nu : Viscosity) :=
  generatedWholeRestartCanonicalReplay (butterflyPhysicalSeed nu)

def butterflyReceipt (nu : Viscosity) :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    (butterflyReplay nu)

theorem butterflyReceipt_target_hasDerivAt_zero (nu : Viscosity) :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath
        (butterflyReceipt nu) (axisWave 4))
      (GaussianRatVector.toComplex (butterflySeedFullFibre 1)) 0 := by
  simpa only [wholeLatticeVorticityFourierTangentAt] using
    (actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      (butterflyReceipt nu) (axisWave 4)).congr_deriv
        (butterflyPhysicalState_wholeTangent_target nu 1)

theorem butterflyTargetTangent_ne_zero :
    GaussianRatVector.toComplex (butterflySeedFullFibre 1) ≠ 0 := by
  rw [butterflySeedFullFibre_eq, butterflyZTwoFullFibre_eq]
  intro rowZero
  have targetZero := congrFun rowZero 2
  norm_num [realRow, realGaussian, GaussianRatVector.toComplex,
    GaussianRat.toComplex, Matrix.cons_val_two] at targetZero

theorem exists_butterflyTargetPersistenceTime (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath
          (butterflyReceipt nu) (axisWave 4) actual ≠ 0 := by
  have punctured :=
    (butterflyReceipt_target_hasDerivAt_zero nu).eventually_ne
      butterflyTargetTangent_ne_zero
      (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in nhds (0 : Real), actual ≠ 0 →
        actualWholeContinuousHeatDuhamelPath
          (butterflyReceipt nu) (axisWave 4) actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

noncomputable def butterflyTargetPersistenceTime
    (nu : Viscosity) : Real :=
  Classical.choose (exists_butterflyTargetPersistenceTime nu)

theorem butterflyTargetPersistenceTime_pos (nu : Viscosity) :
    0 < butterflyTargetPersistenceTime nu :=
  (Classical.choose_spec
    (exists_butterflyTargetPersistenceTime nu)).1

theorem butterflyTargetPersistenceTime_spec
    (nu : Viscosity) (actual : Real)
    (actualPos : 0 < actual)
    (actualLt : actual < butterflyTargetPersistenceTime nu) :
    actualWholeContinuousHeatDuhamelPath
      (butterflyReceipt nu) (axisWave 4) actual ≠ 0 :=
  (Classical.choose_spec
    (exists_butterflyTargetPersistenceTime nu)).2
      actual actualPos actualLt

theorem butterflyPhysicalState_pumpY_ne_zero :
    butterflyPhysicalState 1 pumpY ≠ 0 := by
  rw [butterflyPhysicalState_apply, if_pos (by decide)]
  intro rowZero
  have firstZero := congrFun rowZero 0
  norm_num [butterflySeedRow, pumpY, realRow, realGaussian,
    GaussianRatVector.toComplex, GaussianRat.toComplex,
    Matrix.cons_val_zero] at firstZero

theorem butterflyReceipt_pumpY_zero (nu : Viscosity) :
    actualWholeContinuousHeatDuhamelPath
        (butterflyReceipt nu) pumpY 0 =
      butterflyPhysicalState 1 pumpY := by
  unfold actualWholeContinuousHeatDuhamelPath
    heatDuhamelComplexCoordinatePath
    intervalIntegralComplexCoordinatePath
  simp [butterflyPhysicalSeed_wholeState]

theorem exists_butterflyPumpPersistenceTime (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 ≤ actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath
          (butterflyReceipt nu) pumpY actual ≠ 0 := by
  have pathContinuousAt :=
    (actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      (butterflyReceipt nu) pumpY).continuousAt
  have valueNe :
      actualWholeContinuousHeatDuhamelPath
        (butterflyReceipt nu) pumpY 0 ≠ 0 := by
    rw [butterflyReceipt_pumpY_zero]
    exact butterflyPhysicalState_pumpY_ne_zero
  have nearZero :
      ∀ᶠ actual in nhds (0 : Real),
        actualWholeContinuousHeatDuhamelPath
          (butterflyReceipt nu) pumpY actual ≠ 0 :=
    pathContinuousAt.eventually_ne valueNe
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualNonneg actualLt
  apply withinBall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg actualNonneg]
  exact actualLt

noncomputable def butterflyPumpPersistenceTime
    (nu : Viscosity) : Real :=
  Classical.choose (exists_butterflyPumpPersistenceTime nu)

theorem butterflyPumpPersistenceTime_pos (nu : Viscosity) :
    0 < butterflyPumpPersistenceTime nu :=
  (Classical.choose_spec
    (exists_butterflyPumpPersistenceTime nu)).1

theorem butterflyPumpPersistenceTime_spec
    (nu : Viscosity) (actual : Real)
    (actualNonneg : 0 ≤ actual)
    (actualLt : actual < butterflyPumpPersistenceTime nu) :
    actualWholeContinuousHeatDuhamelPath
      (butterflyReceipt nu) pumpY actual ≠ 0 :=
  (Classical.choose_spec
    (exists_butterflyPumpPersistenceTime nu)).2
      actual actualNonneg actualLt

def butterflyMaterialDuration (nu : Viscosity) : Real :=
  min
      (min (wholeRestartDuration (butterflyPhysicalSeed nu))
        (butterflyTargetPersistenceTime nu))
      (butterflyPumpPersistenceTime nu) / 2

theorem butterflyMaterialDuration_pos (nu : Viscosity) :
    0 < butterflyMaterialDuration nu := by
  unfold butterflyMaterialDuration
  exact div_pos
    (lt_min
      (lt_min (wholeRestartDuration_pos (butterflyPhysicalSeed nu))
        (butterflyTargetPersistenceTime_pos nu))
      (butterflyPumpPersistenceTime_pos nu))
    (by norm_num)

theorem butterflyMaterialDuration_le_original (nu : Viscosity) :
    butterflyMaterialDuration nu ≤
      wholeRestartDuration (butterflyPhysicalSeed nu) := by
  unfold butterflyMaterialDuration
  have outerLe := min_le_left
    (min (wholeRestartDuration (butterflyPhysicalSeed nu))
      (butterflyTargetPersistenceTime nu))
    (butterflyPumpPersistenceTime nu)
  have innerLe := min_le_left
    (wholeRestartDuration (butterflyPhysicalSeed nu))
    (butterflyTargetPersistenceTime nu)
  have minPos := lt_min
    (lt_min (wholeRestartDuration_pos (butterflyPhysicalSeed nu))
      (butterflyTargetPersistenceTime_pos nu))
    (butterflyPumpPersistenceTime_pos nu)
  nlinarith

theorem butterflyMaterialDuration_lt_persistence (nu : Viscosity) :
    butterflyMaterialDuration nu < butterflyTargetPersistenceTime nu := by
  unfold butterflyMaterialDuration
  have outerLe := min_le_left
    (min (wholeRestartDuration (butterflyPhysicalSeed nu))
      (butterflyTargetPersistenceTime nu))
    (butterflyPumpPersistenceTime nu)
  have innerLe := min_le_right
    (wholeRestartDuration (butterflyPhysicalSeed nu))
    (butterflyTargetPersistenceTime nu)
  nlinarith [butterflyTargetPersistenceTime_pos nu]

theorem butterflyMaterialDuration_lt_pumpPersistence (nu : Viscosity) :
    butterflyMaterialDuration nu < butterflyPumpPersistenceTime nu := by
  unfold butterflyMaterialDuration
  have minLe := min_le_right
    (min (wholeRestartDuration (butterflyPhysicalSeed nu))
      (butterflyTargetPersistenceTime nu))
    (butterflyPumpPersistenceTime nu)
  nlinarith [butterflyPumpPersistenceTime_pos nu]

def butterflyMaterialReceipt (nu : Viscosity) :
    WholeContinuousMildSerrinReceipt nu (butterflyPhysicalState 1)
      (butterflyMaterialDuration nu) :=
  restrictWholeContinuousMildSerrinReceipt
    (butterflyMaterialDuration_pos nu)
    (butterflyMaterialDuration_le_original nu)
    (butterflyReceipt nu)

def butterflyMaterialContact (nu : Viscosity) :=
  generatedPositiveWholeRestartContact (butterflyMaterialReceipt nu)

def butterflyMaterialCurrent (nu : Viscosity) :
    GeneratedWholeRestartCurrent nu where
  initialState := butterflyPhysicalState 1
  duration := butterflyMaterialDuration nu
  receipt := butterflyMaterialReceipt nu
  contact := butterflyMaterialContact nu

def butterflyMaterialContactOriginalTime (nu : Viscosity) :
    Set.Icc (0 : Real)
      (wholeRestartDuration (butterflyPhysicalSeed nu)) :=
  commonTimeInclusion (butterflyMaterialDuration_le_original nu)
    (butterflyMaterialContact nu).time

theorem butterflyMaterialContact_target_ne_zero (nu : Viscosity) :
    (butterflyMaterialContact nu).physicalState (axisWave 4) ≠ 0 := by
  change (butterflyReceipt nu).wholePath
    (butterflyMaterialContactOriginalTime nu) (axisWave 4) ≠ 0
  rw [wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    (butterflyReceipt nu) (axisWave 4) (by decide)
      (butterflyMaterialContactOriginalTime nu)]
  apply butterflyTargetPersistenceTime_spec
  · exact (butterflyMaterialContact nu).time_pos
  · exact lt_of_le_of_lt
      (butterflyMaterialContact nu).time.2.2
      (butterflyMaterialDuration_lt_persistence nu)

theorem butterflyMaterialContact_pumpY_ne_zero (nu : Viscosity) :
    (butterflyMaterialContact nu).physicalState pumpY ≠ 0 := by
  change (butterflyReceipt nu).wholePath
    (butterflyMaterialContactOriginalTime nu) pumpY ≠ 0
  rw [wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    (butterflyReceipt nu) pumpY (by decide)
      (butterflyMaterialContactOriginalTime nu)]
  apply butterflyPumpPersistenceTime_spec
  · exact (butterflyMaterialContact nu).time_pos.le
  · exact lt_of_le_of_lt
      (butterflyMaterialContact nu).time.2.2
      (butterflyMaterialDuration_lt_pumpPersistence nu)

/-- The first actual material edge retains the alternating pump and creates
the higher-frequency axis row on the same selected occurrence. -/
theorem butterflyMaterialContact_axisAndPump_active (nu : Viscosity) :
    (butterflyMaterialContact nu).physicalState (axisWave 4) ≠ 0 ∧
      (butterflyMaterialContact nu).physicalState pumpY ≠ 0 :=
  ⟨butterflyMaterialContact_target_ne_zero nu,
    butterflyMaterialContact_pumpY_ne_zero nu⟩

end
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
