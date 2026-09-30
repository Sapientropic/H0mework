import H0mework.Versions.X.NavierStokes.Accumulation.ConcretePhaseRichActionMaterialization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

open scoped BigOperators Matrix Interval

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace PhaseRichTriple

open Matrix
open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteTwoScaleLiftSource
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork

noncomputable section

theorem complexSourceState_zero : complexSourceState 0 = 0 := by
  apply complexSourceState_supported
  rw [sourceIntegerModes_eq_repositoryModes]
  decide

macro "phase_source_row" : tactic =>
  `(tactic| (
    simp_rw [complexSourceState_faithful]
    simp [state, lookup, sourceEntries,
      rowP₁, rowQ₁, rowR₁, rowL₁,
      rowP₂, rowQ₂, rowR₂, rowL₂,
      vectorConj, gConj, g,
      Wave.ofIntegerWavevector,
      GaussianRatVector.toComplex, GaussianRat.toComplex,
      w]))

theorem complexSourceState_transverse :
    WholeStateTransverse complexSourceState := by
  intro wave
  by_cases waveMem : wave ∈ sourceIntegerModes
  · rw [sourceIntegerModes_eq_repositoryModes] at waveMem
    simp only [modes, Finset.mem_insert,
      Finset.mem_singleton] at waveMem
    rcases waveMem with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      phase_source_row <;>
      norm_num [complexWavevector, dotProduct,
        GaussianRatVector.toComplex, GaussianRat.toComplex,
        vectorConj, gConj, g,
        p₁, q₁, r₁, l₁, p₂, q₂, r₂, l₂, waveNeg,
        Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two,
        Complex.mul_re, Complex.mul_im] <;> ring
  · rw [complexSourceState_supported wave waveMem, dotProduct_zero]

theorem sourceIntegerModes_waveNeg_mem_iff
    (wave : IntegerWavevector) :
    waveNeg wave ∈ sourceIntegerModes ↔ wave ∈ sourceIntegerModes := by
  rw [sourceIntegerModes_eq_repositoryModes,
    ← source_support_eq_modes]
  constructor
  · intro negMem
    have twiceNeg := generatedSupport_waveNeg_mem source negMem
    simpa using twiceNeg
  · exact generatedSupport_waveNeg_mem source

theorem complexSourceState_reality :
    FiniteStateFourierReality complexSourceState := by
  intro wave
  by_cases waveMem : wave ∈ sourceIntegerModes
  · rw [sourceIntegerModes_eq_repositoryModes] at waveMem
    simp only [modes, Finset.mem_insert,
      Finset.mem_singleton] at waveMem
    rcases waveMem with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      phase_source_row <;>
      funext coordinate <;>
      fin_cases coordinate <;>
      norm_num [ThreeDimensionalVorticityCoefficientRawSourceCore.vectorConj,
        Complex.star_def,
        GaussianRatVector.toComplex, GaussianRat.toComplex,
        vectorConj, gConj, g,
        p₁, q₁, r₁, l₁, p₂, q₂, r₂, l₂, waveNeg,
        Complex.mul_re, Complex.mul_im]
  · have negNotMem : waveNeg wave ∉ sourceIntegerModes := by
      intro negMem
      exact waveMem ((sourceIntegerModes_waveNeg_mem_iff wave).mp negMem)
    rw [complexSourceState_supported wave waveMem,
      complexSourceState_supported (waveNeg wave) negNotMem]
    exact ThreeDimensionalVorticityCoefficientRawSourceCore.vectorConj_zero.symm

/-- Exact whole coefficient mass of the source-owned physical state. -/
theorem complexSourceState_wholeMass_eq :
    wholeVorticityEuclideanMass complexSourceState = 432 := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    sourceIntegerModes complexSourceState complexSourceState_supported]
  unfold finiteStateVorticityCoefficientEnstrophy
  rw [sourceIntegerModes_eq_sourceWaveModes_image,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  have termEq : ∀ wave ∈ sourceWaveModes,
      complexCoordinateAmplitudeSq
          (complexSourceState wave.toIntegerWavevector) =
        (vectorNormSq (state wave) : ℚ) := by
    intro wave _waveMem
    rw [complexSourceState_faithful]
    simp only [Wave.ofIntegerWavevector_toIntegerWavevector]
    exact (vectorNormSq_toComplex (state wave)).symm
  rw [Finset.sum_congr rfl termEq]
  norm_num [sourceWaveModes, sourceEntries, state, lookup,
    vectorNormSq, GaussianRat.normSq, rowP₁, rowQ₁, rowR₁, rowL₁,
    rowP₂, rowQ₂, rowR₂, rowL₂, vectorConj, gConj, g, w,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- Exact weighted mass retained for quantitative persistence estimates. -/
theorem complexSourceState_gradientMass_eq :
    finiteStateVorticityEnstrophyMass sourceIntegerModes complexSourceState =
      1056 := by
  unfold finiteStateVorticityEnstrophyMass
  rw [sourceIntegerModes_eq_sourceWaveModes_image,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  have termEq : ∀ wave ∈ sourceWaveModes,
      integerWaveNormSq wave.toIntegerWavevector *
          complexCoordinateAmplitudeSq
            (complexSourceState wave.toIntegerWavevector) =
        ((waveNormSq wave * vectorNormSq (state wave) : ℚ) : ℝ) := by
    intro wave _waveMem
    rw [complexSourceState_faithful]
    simp only [Wave.ofIntegerWavevector_toIntegerWavevector,
      ← waveNormSq_cast]
    rw [← vectorNormSq_toComplex]
    norm_num
  rw [Finset.sum_congr rfl termEq]
  norm_num [sourceWaveModes, sourceEntries, state, lookup,
    waveNormSq, vectorNormSq, GaussianRat.normSq,
    rowP₁, rowQ₁, rowR₁, rowL₁, rowP₂, rowQ₂, rowR₂, rowL₂,
    vectorConj, gConj, g, w,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

theorem finiteGenerator_sourceWave_eq
    (wave : Wave)
    (waveMem : wave ∈ sourceWaveModes) :
    finiteStateVorticityGenerator sourceIntegerModes viscosity.coeff
        complexSourceState wave.toIntegerWavevector =
      GaussianRatVector.toComplex (sourceGeneratorAt wave) := by
  rw [sourceGeneratorAt_toComplex]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    sourceIntegerModes complexSourceState complexSourceState_supported]
  rw [finiteStateVorticityGenerator_apply, if_pos]
  exact (sourceWave_mem_iff_integer_mem wave).mp waveMem

/-- The source-generated action materializes as the actual finite generator
pairing on the same physical Fourier occurrence. -/
theorem complexSourceState_generatorRealWork_eq :
    (∑ wave ∈ sourceIntegerModes,
      complexCoordinateRealInner (complexSourceState wave)
        (finiteStateVorticityGenerator sourceIntegerModes viscosity.coeff
          complexSourceState wave)) = (15934 / 125 : Real) := by
  rw [sourceIntegerModes_eq_sourceWaveModes_image,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  calc
    (∑ wave ∈ sourceWaveModes,
        complexCoordinateRealInner
          (complexSourceState wave.toIntegerWavevector)
          (finiteStateVorticityGenerator sourceIntegerModes viscosity.coeff
            complexSourceState wave.toIntegerWavevector)) =
        ((∑ wave ∈ sourceWaveModes,
          vectorRealInner (state wave) (sourceGeneratorAt wave) : ℚ) : ℝ) := by
          rw [Rat.cast_sum]
          apply Finset.sum_congr rfl
          intro wave waveMem
          rw [complexSourceState_faithful]
          simp only [Wave.ofIntegerWavevector_toIntegerWavevector]
          rw [finiteGenerator_sourceWave_eq wave waveMem]
          exact (vectorRealInner_toComplex
            (state wave) (sourceGeneratorAt wave)).symm
    _ = (generatedSourceWork : ℝ) := by
      rw [sourceWaveGeneratorWork_eq_generatedSourceWork]
    _ = (15934 / 125 : ℝ) := by
      rw [generatedSourceWork_eq]
      norm_num

def physicalSeed : SourceOwnedWholeRestartPhysicalSeed viscosity where
  physicalState := complexSourceState
  physicalState_zero := complexSourceState_zero
  transverse := complexSourceState_transverse
  reality := complexSourceState_reality

def replay := generatedWholeRestartCanonicalReplay physicalSeed

def receipt :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt replay

/-- The actual whole receipt reads the source-generated positive action at
time zero.  No contact, persistence radius, or target state is supplied. -/
theorem receipt_netPower_zero_eq :
    actualProjectedWholeNetEnstrophyPower receipt sourceIntegerModes 0 =
      2 * (15934 / 125 : Real) := by
  have sourceReadout :=
    actualProjectedWholeNetEnstrophyPower_zero_eq_generatorRealWork
      receipt sourceIntegerModes complexSourceState_supported
  rw [sourceReadout]
  exact congrArg (fun value : Real => 2 * value)
    complexSourceState_generatorRealWork_eq

theorem receipt_netPower_zero_pos :
    0 < actualProjectedWholeNetEnstrophyPower
      receipt sourceIntegerModes 0 := by
  rw [receipt_netPower_zero_eq]
  norm_num

/-- Half of the exact initial net-power row.  The remaining half is the
source-generated interior margin for the first physical patch. -/
def netPowerFloor : Real := 15934 / 125

theorem netPowerFloor_pos : 0 < netPowerFloor := by
  norm_num [netPowerFloor]

theorem receipt_netPower_initial_patch :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Set.Icc (0 : Real) (wholeRestartDuration physicalSeed),
        actual < epsilon →
          netPowerFloor <
              actualProjectedWholeNetEnstrophyPower
                receipt sourceIntegerModes actual ∧
            wholeVorticityEuclideanMass
                (actualWholeProjectedTransversePath receipt actual).1 < 433 := by
  let netPower : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower
      receipt sourceIntegerModes actual
  let mass : Real → Real := fun actual =>
    wholeVorticityEuclideanMass
      (actualWholeProjectedTransversePath receipt actual).1
  have netPowerContinuous : Continuous netPower :=
    actualProjectedWholeNetEnstrophyPower_continuous
      receipt sourceIntegerModes
  have massContinuous : Continuous mass :=
    continuous_wholeVorticityEuclideanMass.comp
      (continuous_subtype_val.comp
        (actualWholeProjectedTransversePath_continuous receipt))
  have zeroMem : 0 ∈
      {actual | netPowerFloor < netPower actual ∧ mass actual < 433} := by
    constructor
    · change netPowerFloor <
        actualProjectedWholeNetEnstrophyPower
          receipt sourceIntegerModes 0
      rw [receipt_netPower_zero_eq]
      change netPowerFloor < 2 * netPowerFloor
      linarith [netPowerFloor_pos]
    · change wholeVorticityEuclideanMass
          (actualWholeProjectedTransversePath receipt 0).1 < 433
      have stateAtZero :
          (actualWholeProjectedTransversePath receipt 0).1 =
            complexSourceState := by
        change receipt.wholePath
            (Set.projIcc (0 : Real) (wholeRestartDuration physicalSeed)
              receipt.requestedTimePos.le 0) = complexSourceState
        rw [Set.projIcc_of_mem receipt.requestedTimePos.le
          ⟨le_rfl, receipt.requestedTimePos.le⟩]
        exact receipt.wholePath_initial
      rw [stateAtZero, complexSourceState_wholeMass_eq]
      norm_num
  have neighborhoodOpen :
      IsOpen {actual |
        netPowerFloor < netPower actual ∧ mass actual < 433} :=
    (isOpen_lt continuous_const netPowerContinuous).inter
      (isOpen_lt massContinuous continuous_const)
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

noncomputable def netPowerPatchTime : Real :=
  Classical.choose receipt_netPower_initial_patch

theorem netPowerPatchTime_pos : 0 < netPowerPatchTime :=
  (Classical.choose_spec receipt_netPower_initial_patch).1

theorem netPowerPatchTime_spec
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration physicalSeed))
    (actualLt : actual < netPowerPatchTime) :
    netPowerFloor <
        actualProjectedWholeNetEnstrophyPower
          receipt sourceIntegerModes actual ∧
      wholeVorticityEuclideanMass
          (actualWholeProjectedTransversePath receipt actual).1 < 433 :=
  (Classical.choose_spec receipt_netPower_initial_patch).2
    actual actualMem actualLt

/-- The source compiler itself restricts the seed to its generated positive
action patch.  The patch time is not a field of the public current. -/
def shortDuration : Real :=
  min (wholeRestartDuration physicalSeed) netPowerPatchTime / 2

theorem shortDuration_pos : 0 < shortDuration := by
  unfold shortDuration
  exact div_pos
    (lt_min (wholeRestartDuration_pos physicalSeed) netPowerPatchTime_pos)
    (by norm_num)

theorem shortDuration_le_original :
    shortDuration ≤ wholeRestartDuration physicalSeed := by
  unfold shortDuration
  have minLe := min_le_left
    (wholeRestartDuration physicalSeed) netPowerPatchTime
  have minPos : 0 < min
      (wholeRestartDuration physicalSeed) netPowerPatchTime :=
    lt_min (wholeRestartDuration_pos physicalSeed) netPowerPatchTime_pos
  nlinarith

theorem shortDuration_lt_patch : shortDuration < netPowerPatchTime := by
  unfold shortDuration
  have minLe := min_le_right
    (wholeRestartDuration physicalSeed) netPowerPatchTime
  nlinarith [netPowerPatchTime_pos]

def shortReceipt :
    WholeContinuousMildSerrinReceipt viscosity complexSourceState
      shortDuration :=
  restrictWholeContinuousMildSerrinReceipt
    shortDuration_pos shortDuration_le_original receipt

def shortContact := generatedPositiveWholeRestartContact shortReceipt

/-- Source-selected physical current whose contact endpoint retains the
positive phase-rich action instruction. -/
def sourceSelectedInitial : GeneratedWholeRestartCurrent viscosity where
  initialState := complexSourceState
  duration := shortDuration
  receipt := shortReceipt
  contact := shortContact

theorem shortContact_prefix_netPower_gt_floor
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real) shortContact.time.1) :
    netPowerFloor <
      actualProjectedWholeNetEnstrophyPower
        shortContact.prefixReceipt sourceIntegerModes actual := by
  have actualLeShort : actual ≤ shortDuration :=
    actualMem.2.trans shortContact.time.2.2
  have actualMemOriginal : actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration physicalSeed) :=
    ⟨actualMem.1, actualLeShort.trans shortDuration_le_original⟩
  have actualLtPatch : actual < netPowerPatchTime :=
    actualLeShort.trans_lt shortDuration_lt_patch
  have stateEq :
      (actualWholeProjectedTransversePath
        shortContact.prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath receipt actual).1 := by
    change shortContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) shortContact.time.1
          shortContact.time_pos.le actual) =
      receipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration physicalSeed)
          receipt.requestedTimePos.le actual)
    rw [Set.projIcc_of_mem shortContact.time_pos.le actualMem]
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le actualMemOriginal]
    rfl
  have sourcePositive := netPowerPatchTime_spec
    actual actualMemOriginal actualLtPatch
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [stateEq]
  exact sourcePositive.1

/-- The fixed native successor reads the same positive instruction at time
zero.  This is the seed of the local recursive invariant, not a future
recurrence premise. -/
theorem sourceSelectedInitial_nextReceipt_netPower_zero_gt_floor :
    netPowerFloor <
      actualProjectedWholeNetEnstrophyPower
        sourceSelectedInitial.nextReceipt sourceIntegerModes 0 := by
  have terminalPositive := shortContact_prefix_netPower_gt_floor
    shortContact.time.1 ⟨shortContact.time_pos.le, le_rfl⟩
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          sourceSelectedInitial.nextReceipt sourceIntegerModes 0 =
        actualProjectedWholeNetEnstrophyPower
          shortContact.prefixReceipt sourceIntegerModes
          shortContact.time.1 := by
    simpa only [sourceSelectedInitial] using
      nextReceipt_netPower_zero_eq_contact_selectedEndpoint
        sourceSelectedInitial sourceIntegerModes
  rwa [powerEq]

theorem sourceIntegerModes_zero_not_mem :
    (0 : IntegerWavevector) ∉ sourceIntegerModes := by
  rw [sourceIntegerModes_eq_repositoryModes]
  decide

theorem complexSourceState_finiteMass_eq :
    finiteStateVorticityCoefficientEnstrophy
      sourceIntegerModes complexSourceState = 432 := by
  have massEq := complexSourceState_wholeMass_eq
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    sourceIntegerModes complexSourceState complexSourceState_supported] at massEq
  exact massEq

/-- The selected source contact pays a strictly positive physical debit on
its complete finite action row. -/
theorem shortContact_prefix_netPower_integral_pos :
    0 < ∫ actual in (0 : Real)..shortContact.time.1,
      actualProjectedWholeNetEnstrophyPower
        shortContact.prefixReceipt sourceIntegerModes actual := by
  have pointwise :
      ∀ actual ∈ Set.Icc (0 : Real) shortContact.time.1,
        netPowerFloor ≤
          actualProjectedWholeNetEnstrophyPower
            shortContact.prefixReceipt sourceIntegerModes actual := by
    intro actual actualMem
    exact (shortContact_prefix_netPower_gt_floor actual actualMem).le
  have lower := intervalIntegral.integral_mono_on
    (μ := volume) shortContact.time_pos.le
    (continuous_const.intervalIntegrable 0 shortContact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      shortContact.prefixReceipt sourceIntegerModes).intervalIntegrable
        0 shortContact.time.1)
    pointwise
  have normalized :
      netPowerFloor * shortContact.time.1 ≤
        ∫ actual in (0 : Real)..shortContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            shortContact.prefixReceipt sourceIntegerModes actual := by
    simpa [intervalIntegral.integral_const, smul_eq_mul,
      mul_comm] using lower
  exact (mul_pos netPowerFloor_pos shortContact.time_pos).trans_le normalized

theorem shortContact_finiteMass_gt_source :
    (432 : Real) <
      finiteStateVorticityCoefficientEnstrophy
        sourceIntegerModes shortContact.physicalState := by
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      shortContact.prefixReceipt sourceIntegerModes
      sourceIntegerModes_zero_not_mem
  rw [shortContact.prefixReceipt_terminal] at ledger
  rw [complexSourceState_finiteMass_eq] at ledger
  have gain := shortContact_prefix_netPower_integral_pos
  linarith

theorem shortContact_wholeMass_gt_source :
    (432 : Real) < wholeVorticityEuclideanMass shortContact.physicalState := by
  exact shortContact_finiteMass_gt_source.trans_le
    (finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      sourceIntegerModes shortContact.physicalState)

theorem shortContact_wholeMass_lt_433 :
    wholeVorticityEuclideanMass shortContact.physicalState < 433 := by
  have actualMemOriginal : shortContact.time.1 ∈ Set.Icc (0 : Real)
      (wholeRestartDuration physicalSeed) :=
    ⟨shortContact.time_pos.le,
      shortContact.time.2.2.trans shortDuration_le_original⟩
  have actualLtPatch : shortContact.time.1 < netPowerPatchTime :=
    shortContact.time.2.2.trans_lt shortDuration_lt_patch
  have sourceBound :=
    (netPowerPatchTime_spec shortContact.time.1
      actualMemOriginal actualLtPatch).2
  have stateEq :
      (actualWholeProjectedTransversePath receipt shortContact.time.1).1 =
        shortContact.physicalState := by
    calc
      (actualWholeProjectedTransversePath receipt shortContact.time.1).1 =
          (actualWholeProjectedTransversePath
            shortContact.prefixReceipt shortContact.time.1).1 := by
        change receipt.wholePath
            (Set.projIcc (0 : Real) (wholeRestartDuration physicalSeed)
              receipt.requestedTimePos.le shortContact.time.1) =
          shortContact.prefixReceipt.wholePath
            (Set.projIcc (0 : Real) shortContact.time.1
              shortContact.time_pos.le shortContact.time.1)
        rw [Set.projIcc_of_mem receipt.requestedTimePos.le actualMemOriginal]
        rw [Set.projIcc_of_mem shortContact.time_pos.le
          ⟨shortContact.time_pos.le, le_rfl⟩]
        rfl
      _ = shortContact.physicalState :=
        by
          change shortContact.prefixReceipt.wholePath
              (Set.projIcc (0 : Real) shortContact.time.1
                shortContact.time_pos.le shortContact.time.1) =
            shortContact.physicalState
          rw [Set.projIcc_of_mem shortContact.time_pos.le
            ⟨shortContact.time_pos.le, le_rfl⟩]
          exact shortContact.prefixReceipt_terminal
  rwa [stateEq] at sourceBound

/-- Positive source-owned charge already paid on the edge that produces the
selected initial occurrence.  It is retained as the finite seed of the
recursive invariant; no future edge or recurrence is stored here. -/
def predecessorScaleRelativeCharge : Real :=
  netPowerFloor * shortContact.time.1 *
    (433 : Real) ^ (11 / 2 : Real)

theorem predecessorScaleRelativeCharge_pos :
    0 < predecessorScaleRelativeCharge := by
  unfold predecessorScaleRelativeCharge
  exact mul_pos
    (mul_pos netPowerFloor_pos shortContact.time_pos)
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem predecessor_scaleRelativeMassDebit :
    predecessorScaleRelativeCharge /
          (wholeVorticityEuclideanMass complexSourceState + 1) ^
            (11 / 2 : Real) ≤
      wholeVorticityEuclideanMass shortContact.physicalState -
        wholeVorticityEuclideanMass complexSourceState := by
  have finiteGain :
      netPowerFloor * shortContact.time.1 ≤
        finiteStateVorticityCoefficientEnstrophy
            sourceIntegerModes shortContact.physicalState -
          finiteStateVorticityCoefficientEnstrophy
            sourceIntegerModes complexSourceState := by
    have ledger :=
      actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
        shortContact.prefixReceipt sourceIntegerModes
        sourceIntegerModes_zero_not_mem
    rw [shortContact.prefixReceipt_terminal] at ledger
    have lower := intervalIntegral.integral_mono_on
      (μ := volume) shortContact.time_pos.le
      (continuous_const.intervalIntegrable 0 shortContact.time.1)
      ((actualProjectedWholeNetEnstrophyPower_continuous
        shortContact.prefixReceipt sourceIntegerModes).intervalIntegrable
          0 shortContact.time.1)
      (fun actual actualMem =>
        (shortContact_prefix_netPower_gt_floor actual actualMem).le)
    have normalized :
        netPowerFloor * shortContact.time.1 ≤
          ∫ actual in (0 : Real)..shortContact.time.1,
            actualProjectedWholeNetEnstrophyPower
              shortContact.prefixReceipt sourceIntegerModes actual := by
      simpa [intervalIntegral.integral_const, smul_eq_mul,
        mul_comm] using lower
    linarith
  have wholeGain :
      netPowerFloor * shortContact.time.1 ≤
        wholeVorticityEuclideanMass shortContact.physicalState -
          wholeVorticityEuclideanMass complexSourceState := by
    rw [wholeVorticityEuclideanMass_eq_finite_of_supported
      sourceIntegerModes complexSourceState complexSourceState_supported]
    linarith [finiteGain,
      finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        sourceIntegerModes shortContact.physicalState]
  have baseEq :
      wholeVorticityEuclideanMass complexSourceState + 1 = 433 := by
    rw [complexSourceState_wholeMass_eq]
    norm_num
  rw [baseEq, predecessorScaleRelativeCharge]
  have denominatorNe :
      (433 : Real) ^ (11 / 2 : Real) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  rw [mul_div_cancel_right₀ _ denominatorNe]
  exact wholeGain

def contact := generatedPositiveWholeRestartContact receipt

/-- Default phase-rich current used by downstream recurrence work. -/
def current : GeneratedWholeRestartCurrent viscosity := sourceSelectedInitial

end

end PhaseRichTriple
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
