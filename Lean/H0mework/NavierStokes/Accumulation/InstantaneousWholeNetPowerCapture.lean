import H0mework.NavierStokes.Accumulation.TemporalEnstrophyLedger
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeViscousNegativeOne
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeNonlinearNegativeOne
import H0mework.NavierStokes.Crossing.TangentCoercivity

/-!
# Source-generated joint mass/work capture

One actual current generates a finite inventory that simultaneously captures
its coefficient mass and approximates its signed global time-zero
net-enstrophy work.  The signed row is part of the chooser predicate; it is
never inferred from false Finset power monotonicity.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture

open Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact

noncomputable section

/-- The global instantaneous physical net-work row at one whole state. -/
def instantaneousWholeNetPowerRow
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : Real :=
  2 * complexCoordinateRealInner (state wave)
      (wholeStateVorticityNonlinearCoefficientAt state wave) -
    2 * complexCoordinateRealInner (state wave)
      ((nu.coeff * integerWaveViscousMultiplier wave) • state wave)

private theorem complexCoordinateRealInner_real_smul_left
    (scalar : Real)
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scalar • left) right =
      scalar * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, Complex.smul_re, Complex.smul_im]
  ring

private theorem complexCoordinateRealInner_real_smul_right_probe
    (scalar : Real)
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left (scalar • right) =
      scalar * complexCoordinateRealInner left right := by
  exact complexCoordinateRealInner_real_smul_right left right scalar

/-- Full-wave Euclideanization of the existing coefficient Hilbert state.
The factor three is only the finite coordinate-norm comparison. -/
def wholeEuclideanize
    (state : ComplexVorticityHilbertState) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateEuclidean) 2 :=
  ⟨fun wave => euclideanCoordinateRow (state wave), by
    apply memℓp_gen
    have stateNormSqSummable :
        Summable fun wave : IntegerWavevector => ‖state wave‖ ^ (2 : Nat) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        state.2.summable (by norm_num)
    have upperSummable :
        Summable fun wave : IntegerWavevector => 3 * ‖state wave‖ ^ (2 : Nat) :=
      stateNormSqSummable.mul_left 3
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      upperSummable.of_nonneg_of_le
        (fun wave => sq_nonneg ‖euclideanCoordinateRow (state wave)‖)
        (fun wave => by
          rw [euclideanCoordinateRow_norm_sq]
          exact complexCoordinateAmplitudeSq_le_three_mul_norm_sq
            (state wave))⟩

@[simp] theorem wholeEuclideanize_apply
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    wholeEuclideanize state wave = euclideanCoordinateRow (state wave) := rfl

/-- The actual positive-one vorticity row and unforced negative-one tangent
are both existing whole states; only their finite coordinate norm is changed. -/
def wholeGradientEuclideanState
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateEuclidean) 2 :=
  wholeEuclideanize
    (wholeStateVorticityViscousNegativeOneState
      1 state gradientSummable)

def wholeUnforcedNegativeOneEuclideanState
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateEuclidean) 2 :=
  wholeEuclideanize
    (wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable -
      wholeStateVorticityViscousNegativeOneState
        nu.coeff state gradientSummable)

theorem instantaneousWholeNetPowerRow_eq_weighted_inner
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (zeroRow : state 0 = 0)
    (wave : IntegerWavevector) :
    instantaneousWholeNetPowerRow nu state wave =
      2 * (inner Complex
        (wholeGradientEuclideanState state gradientSummable wave)
        (wholeUnforcedNegativeOneEuclideanState
          nu state stateTransverse gradientSummable wave)).re := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [instantaneousWholeNetPowerRow, wholeGradientEuclideanState,
      wholeUnforcedNegativeOneEuclideanState, wholeEuclideanize,
      wholeStateVorticityViscousNegativeOneWeightedCoefficient,
      integerWaveViscousMultiplier, integerWaveNormSq, zeroRow]
    rw [show euclideanCoordinateRow (0 : ComplexCoordinateVector) = 0 by rfl,
      inner_zero_left]
    simp [complexCoordinateRealInner,
      ThreeDimensionalVorticityCoefficientStretchingPairTable.complexCoordinateVectorNormSq]
  · have nonlinearRecovery :=
      sqrt_viscousMultiplier_smul_wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
        state wave waveZero
    have viscousRecovery :=
      sqrt_viscousMultiplier_smul_wholeStateVorticityViscousNegativeOneState_apply
        nu.coeff state gradientSummable wave
    have recovery :
        Real.sqrt (integerWaveViscousMultiplier wave) •
            (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state wave -
              wholeStateVorticityViscousNegativeOneWeightedCoefficient
                nu.coeff state wave) =
          wholeStateVorticityNonlinearCoefficientAt state wave -
            (nu.coeff * integerWaveViscousMultiplier wave) • state wave := by
      rw [smul_sub, nonlinearRecovery]
      congr 1
    rw [wholeGradientEuclideanState,
      wholeUnforcedNegativeOneEuclideanState,
      wholeEuclideanize_apply, wholeEuclideanize_apply,
      euclideanCoordinateRow_re_inner]
    simp only [wholeStateVorticityViscousNegativeOneState_apply,
      wholeStateVorticityViscousNegativeOneWeightedCoefficient,
      one_mul]
    rw [complexCoordinateRealInner_real_smul_left]
    rw [← complexCoordinateRealInner_real_smul_right_probe]
    change instantaneousWholeNetPowerRow nu state wave =
      2 * complexCoordinateRealInner (state wave)
        (Real.sqrt (integerWaveViscousMultiplier wave) •
          (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state wave -
            wholeStateVorticityViscousNegativeOneWeightedCoefficient
              nu.coeff state wave))
    rw [recovery]
    unfold instantaneousWholeNetPowerRow
    rw [complexCoordinateRealInner_sub_right]
    ring

/-- The global instantaneous net-work row is absolutely summable on every
actual gradient-summable whole state. -/
theorem summable_instantaneousWholeNetPowerRow
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (zeroRow : state 0 = 0) :
    Summable (instantaneousWholeNetPowerRow nu state) := by
  let positive := wholeGradientEuclideanState state gradientSummable
  let negative := wholeUnforcedNegativeOneEuclideanState
    nu state stateTransverse gradientSummable
  have innerHasSum := lp.hasSum_inner (𝕜 := Complex) positive negative
  have realHasSum := innerHasSum.map Complex.reCLM Complex.reCLM.continuous
  have scaledSummable :
      Summable fun wave : IntegerWavevector =>
        2 * (inner Complex (positive wave) (negative wave)).re :=
    realHasSum.mul_left 2 |>.summable
  exact scaledSummable.congr fun wave => by
    symm
    exact instantaneousWholeNetPowerRow_eq_weighted_inner
      nu state stateTransverse gradientSummable zeroRow wave

theorem instantaneousWholeNetPowerRow_zero
    (nu : Viscosity)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    instantaneousWholeNetPowerRow nu state 0 = 0 := by
  simp [instantaneousWholeNetPowerRow, zeroRow,
    complexCoordinateRealInner]

private theorem sum_erase_zero_eq
    {index : Type*}
    [DecidableEq index]
    [Zero index]
    (f : index → Real)
    (fZero : f 0 = 0)
    (modes : Finset index) :
    ∑ i ∈ modes.erase 0, f i = ∑ i ∈ modes, f i := by
  by_cases zeroMem : 0 ∈ modes
  · rw [← Finset.sum_erase_add _ _ zeroMem, fZero, add_zero]
  · rw [Finset.erase_eq_of_notMem zeroMem]

/-- Every finite projected time-zero power is exactly the finite sum of the
same global instantaneous row; the inventory does not alter input data. -/
theorem actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualProjectedWholeNetEnstrophyPower receipt modes 0 =
      ∑ wave ∈ modes, instantaneousWholeNetPowerRow nu initialState wave := by
  have stateAtZero :
      (actualWholeProjectedTransversePath receipt 0).1 = initialState := by
    change receipt.wholePath
        (Set.projIcc (0 : Real) requestedTime
          receipt.requestedTimePos.le 0) = initialState
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      ⟨le_rfl, receipt.requestedTimePos.le⟩]
    exact receipt.wholePath_initial
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [stateAtZero, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [complexSharpSupportProjection_apply, if_pos waveMem]
  rfl

/-- Pure summable-row joint capture.  The generated finite set contains a
requested base inventory, captures a nonnegative mass row and approximates
the signed global work sum with an independently specified error. -/
theorem exists_joint_finite_capture
    {index : Type*}
    [DecidableEq index]
    (mass work : index → Real)
    (massSummable : Summable mass)
    (workSummable : Summable work)
    (massNonneg : ∀ i, 0 ≤ mass i)
    (base : Finset index)
    {massTolerance workTolerance : Real}
    (massTolerancePos : 0 < massTolerance)
    (workTolerancePos : 0 < workTolerance) :
    ∃ modes : Finset index,
      base ⊆ modes ∧
      (∑' i : {i : index // i ∉ modes}, mass i.1) < massTolerance ∧
      |(∑' i, work i) - ∑ i ∈ modes, work i| < workTolerance := by
  have massConverges :
      Tendsto (fun modes : Finset index => ∑ i ∈ modes, mass i)
        Filter.atTop (nhds (∑' i, mass i)) :=
    massSummable.hasSum
  have workConverges :
      Tendsto (fun modes : Finset index => ∑ i ∈ modes, work i)
        Filter.atTop (nhds (∑' i, work i)) :=
    workSummable.hasSum
  have massEventually : ∀ᶠ modes : Finset index in Filter.atTop,
      |(∑' i, mass i) - ∑ i ∈ modes, mass i| < massTolerance := by
    have close := (Metric.tendsto_nhds.1 massConverges)
      massTolerance massTolerancePos
    filter_upwards [close] with modes modesClose
    simpa only [Real.dist_eq, abs_sub_comm] using modesClose
  have workEventually : ∀ᶠ modes : Finset index in Filter.atTop,
      |(∑' i, work i) - ∑ i ∈ modes, work i| < workTolerance := by
    have close := (Metric.tendsto_nhds.1 workConverges)
      workTolerance workTolerancePos
    filter_upwards [close] with modes modesClose
    simpa only [Real.dist_eq, abs_sub_comm] using modesClose
  have baseEventually : ∀ᶠ modes : Finset index in Filter.atTop,
      base ⊆ modes := Filter.eventually_ge_atTop base
  rcases (massEventually.and (workEventually.and baseEventually)).exists with
    ⟨modes, massClose, workClose, baseSubset⟩
  refine ⟨modes, baseSubset, ?_, workClose⟩
  have split := massSummable.sum_add_tsum_subtype_compl modes
  have finiteLe : (∑ i ∈ modes, mass i) ≤ ∑' i, mass i :=
    massSummable.sum_le_tsum modes (fun i _ => massNonneg i)
  have tailEq :
      (∑' i : {i : index // i ∉ modes}, mass i.1) =
        (∑' i, mass i) - ∑ i ∈ modes, mass i := by
    linarith
  rw [tailEq]
  rw [abs_of_nonneg (sub_nonneg.mpr finiteLe)] at massClose
  exact massClose

/-- One actual restart current has a source-generated summable global
instantaneous work row.  This is stronger than the existing integrated
`actualWholeRowNetWork` summability and is indexed by the same time-zero
physical state read by `current.nextReceipt`. -/
theorem summable_current_instantaneousWholeNetPowerRow
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    Summable
      (instantaneousWholeNetPowerRow nu current.contact.physicalState) := by
  exact summable_instantaneousWholeNetPowerRow
    nu current.contact.physicalState current.contact.transverse
      current.contact.gradient_summable current.contact.physicalState_zero

/-- Canonical finite projections converge to the same current's global
instantaneous work. -/
theorem current_projectedPower_zero_tendsto_global
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    Tendsto
      (fun modes : Finset IntegerWavevector =>
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes 0)
      Filter.atTop
      (nhds
        (∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave)) := by
  rw [show
    (fun modes : Finset IntegerWavevector =>
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0) =
      (fun modes : Finset IntegerWavevector =>
        ∑ wave ∈ modes,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave) by
      funext modes
      exact
        actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow
          current.nextReceipt modes]
  exact (summable_current_instantaneousWholeNetPowerRow current).hasSum

/-- Joint current-owned finite capture: the chosen inventory may be required
to contain any already generated base.  Hence signed work is certified on
the final enlarged inventory rather than inferred by false Finset
monotonicity. -/
theorem exists_current_jointMassPowerCapture
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    {massTolerance workTolerance : Real}
    (massTolerancePos : 0 < massTolerance)
    (workTolerancePos : 0 < workTolerance) :
    ∃ modes : Finset IntegerWavevector,
      base ⊆ modes ∧
      wholeTailVorticityMass modes current.contact.physicalState <
        massTolerance ∧
      |(∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave) -
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes 0| < workTolerance := by
  have massSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq
          (current.contact.physicalState wave) :=
    (summable_vorticityRowAmplitude_sq
      current.contact.physicalState).congr fun wave => by
        rw [vorticityRowAmplitude_sq,
          complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rcases exists_joint_finite_capture
      (fun wave => complexCoordinateAmplitudeSq
        (current.contact.physicalState wave))
      (instantaneousWholeNetPowerRow nu current.contact.physicalState)
      massSummable
      (summable_current_instantaneousWholeNetPowerRow current)
      (fun wave => complexCoordinateAmplitudeSq_nonneg
        (current.contact.physicalState wave))
      base massTolerancePos workTolerancePos with
    ⟨modes, baseSubset, tailSmall, workClose⟩
  refine ⟨modes, baseSubset, ?_, ?_⟩
  · exact tailSmall
  · rw [actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow]
    exact workClose

/-- Direct replacement shape for `currentMassCaptureModesAtTolerance`: the
inventory is zero-free, contains the already generated zero-free base, and
the signed finite power is certified after the enlargement itself. -/
theorem exists_current_jointMassPowerCapture_zeroFree
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (baseZeroNotMem : (0 : IntegerWavevector) ∉ base)
    {massTolerance workTolerance : Real}
    (massTolerancePos : 0 < massTolerance)
    (workTolerancePos : 0 < workTolerance) :
    ∃ modes : Finset IntegerWavevector,
      base ⊆ modes ∧
      (0 : IntegerWavevector) ∉ modes ∧
      wholeTailVorticityMass modes current.contact.physicalState <
        massTolerance ∧
      |(∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave) -
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes 0| < workTolerance := by
  rcases exists_current_jointMassPowerCapture current base
      massTolerancePos workTolerancePos with
    ⟨modes, baseSubset, tailSmall, workClose⟩
  let clean := modes.erase 0
  have baseClean : base ⊆ clean := by
    intro wave waveMem
    exact Finset.mem_erase.mpr
      ⟨fun waveZero => baseZeroNotMem (waveZero ▸ waveMem),
        baseSubset waveMem⟩
  have cleanZero : (0 : IntegerWavevector) ∉ clean :=
    Finset.notMem_erase 0 modes
  have massZero :
      complexCoordinateAmplitudeSq (current.contact.physicalState 0) = 0 := by
    rw [current.contact.physicalState_zero]
    simp [complexCoordinateAmplitudeSq]
  have finiteMassClean :
      finiteStateVorticityCoefficientEnstrophy clean
          current.contact.physicalState =
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact sum_erase_zero_eq
      (fun wave => complexCoordinateAmplitudeSq
        (current.contact.physicalState wave)) massZero modes
  have tailClean :
      wholeTailVorticityMass clean current.contact.physicalState =
        wholeTailVorticityMass modes current.contact.physicalState := by
    rw [wholeTailVorticityMass_eq_whole_sub_finite,
      wholeTailVorticityMass_eq_whole_sub_finite, finiteMassClean]
  have workZero := instantaneousWholeNetPowerRow_zero
    nu current.contact.physicalState current.contact.physicalState_zero
  have finiteWorkClean :
      actualProjectedWholeNetEnstrophyPower current.nextReceipt clean 0 =
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 := by
    rw [actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow,
      actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow]
    exact sum_erase_zero_eq
      (instantaneousWholeNetPowerRow nu current.contact.physicalState)
      workZero modes
  refine ⟨clean, baseClean, cleanZero, ?_, ?_⟩
  · rwa [tailClean]
  · rwa [finiteWorkClean]

/-- Source-owned selector whose defining predicate already contains the
requested base inventory, tail capture and signed power approximation.  The
base is cleaned at zero internally, so no proof argument enters the data. -/
noncomputable def currentJointMassPowerCaptureModesAtTolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (tolerance : { value : Real // 0 < value }) :
    Finset IntegerWavevector :=
  Classical.choose
    (exists_current_jointMassPowerCapture_zeroFree
      current (base.erase 0) (Finset.notMem_erase 0 base)
      tolerance.2 tolerance.2)

theorem currentJointMassPowerCaptureModesAtTolerance_cleanBase_subset
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (tolerance : { value : Real // 0 < value }) :
    base.erase 0 ⊆
      currentJointMassPowerCaptureModesAtTolerance current base tolerance :=
  (Classical.choose_spec
    (exists_current_jointMassPowerCapture_zeroFree
      current (base.erase 0) (Finset.notMem_erase 0 base)
      tolerance.2 tolerance.2)).1

theorem currentJointMassPowerCaptureModesAtTolerance_base_subset
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (baseZeroNotMem : (0 : IntegerWavevector) ∉ base)
    (tolerance : { value : Real // 0 < value }) :
    base ⊆
      currentJointMassPowerCaptureModesAtTolerance current base tolerance := by
  intro wave waveMem
  apply currentJointMassPowerCaptureModesAtTolerance_cleanBase_subset
  exact Finset.mem_erase.mpr
    ⟨fun waveZero => baseZeroNotMem (waveZero ▸ waveMem), waveMem⟩

theorem currentJointMassPowerCaptureModesAtTolerance_zeroNotMem
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (tolerance : { value : Real // 0 < value }) :
    (0 : IntegerWavevector) ∉
      currentJointMassPowerCaptureModesAtTolerance current base tolerance :=
  (Classical.choose_spec
    (exists_current_jointMassPowerCapture_zeroFree
      current (base.erase 0) (Finset.notMem_erase 0 base)
      tolerance.2 tolerance.2)).2.1

theorem currentJointMassPowerCaptureModesAtTolerance_tail_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (tolerance : { value : Real // 0 < value }) :
    wholeTailVorticityMass
        (currentJointMassPowerCaptureModesAtTolerance current base tolerance)
        current.contact.physicalState < tolerance.1 :=
  (Classical.choose_spec
    (exists_current_jointMassPowerCapture_zeroFree
      current (base.erase 0) (Finset.notMem_erase 0 base)
      tolerance.2 tolerance.2)).2.2.1

theorem currentJointMassPowerCaptureModesAtTolerance_power_close
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (tolerance : { value : Real // 0 < value }) :
    |(∑' wave : IntegerWavevector,
        instantaneousWholeNetPowerRow
          nu current.contact.physicalState wave) -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt
        (currentJointMassPowerCaptureModesAtTolerance
          current base tolerance) 0| < tolerance.1 :=
  (Classical.choose_spec
    (exists_current_jointMassPowerCapture_zeroFree
      current (base.erase 0) (Finset.notMem_erase 0 base)
      tolerance.2 tolerance.2)).2.2.2

/-- Conditional local factorization of a specified time-zero power margin.
The condition names the exact remaining source equation: positivity of the
global instantaneous whole work above the requested margin.  It is not a
lawful final premise; a concrete source producer would have to prove it. -/
theorem exists_current_jointMassPowerCapture_above
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (threshold : Real)
    {massTolerance workTolerance : Real}
    (massTolerancePos : 0 < massTolerance)
    (workTolerancePos : 0 < workTolerance)
    (globalHeadroom :
      threshold + workTolerance <
        ∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave) :
    ∃ modes : Finset IntegerWavevector,
      base ⊆ modes ∧
      wholeTailVorticityMass modes current.contact.physicalState <
        massTolerance ∧
      threshold < actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes 0 := by
  rcases exists_current_jointMassPowerCapture current base
      massTolerancePos workTolerancePos with
    ⟨modes, baseSubset, tailSmall, workClose⟩
  refine ⟨modes, baseSubset, tailSmall, ?_⟩
  rcases abs_lt.mp workClose with ⟨lower, _upper⟩
  linarith

theorem exists_current_jointMassPowerCapture_zeroFree_above
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (base : Finset IntegerWavevector)
    (baseZeroNotMem : (0 : IntegerWavevector) ∉ base)
    (threshold : Real)
    {massTolerance workTolerance : Real}
    (massTolerancePos : 0 < massTolerance)
    (workTolerancePos : 0 < workTolerance)
    (globalHeadroom :
      threshold + workTolerance <
        ∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave) :
    ∃ modes : Finset IntegerWavevector,
      base ⊆ modes ∧
      (0 : IntegerWavevector) ∉ modes ∧
      wholeTailVorticityMass modes current.contact.physicalState <
        massTolerance ∧
      threshold < actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes 0 := by
  rcases exists_current_jointMassPowerCapture_zeroFree current base
      baseZeroNotMem massTolerancePos workTolerancePos with
    ⟨modes, baseSubset, zeroNotMem, tailSmall, workClose⟩
  refine ⟨modes, baseSubset, zeroNotMem, tailSmall, ?_⟩
  rcases abs_lt.mp workClose with ⟨lower, _upper⟩
  linarith

end

end ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
end NavierStokes
end SaturationMonoid
