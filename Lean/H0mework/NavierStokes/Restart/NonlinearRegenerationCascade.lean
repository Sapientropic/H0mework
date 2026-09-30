import H0mework.NavierStokes.Restart.NonlinearDuhamelRegeneration
import H0mework.NavierStokes.Restart.FiniteTimeObstruction
import H0mework.NavierStokes.Crossing.TangentCoercivity

/-!
# Nonlinear regeneration forced by finite-time restart accumulation

Each native whole restart has the exact same-event decomposition

```text
next physical state
  = homogeneous heat evolution of the current state
  + actual nonlinear Duhamel regeneration.
```

The heat term is contractive on the complete Fourier `ℓ²` carrier.  Hence
summability of the actual regeneration norms would uniformly bound every
physical contact state.  The existing finite-time obstruction then gives
the source-owned conclusion

```text
bounded accumulated physical time
  → the actual nonlinear regeneration norms are not summable.
```

No restart horizon, cutoff, margin, branch, target path, forcing, or
continuation certificate enters the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade

open scoped BigOperators ENNReal

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity

noncomputable section

/-! ## Whole-carrier heat transport -/

/-- Homogeneous vorticity heat evolution on the complete Fourier carrier.
The nonnegative duration is carried by its type, and viscosity positivity is
owned by `Viscosity`. -/
def wholeVorticityHeatEvolution
    (ν : Viscosity)
    (duration : NNReal)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  ⟨fun wave =>
      finiteStateVorticityHeatMultiplier
        ν.coeff duration.1 wave • state wave,
    by
      have stateSummable :
          Summable fun wave : IntegerWavevector => ‖state wave‖ ^ 2 := by
        simpa using
          (lp.hasSum_norm (p := (2 : ℝ≥0∞))
            (by norm_num) state).summable
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        stateSummable.of_nonneg_of_le
          (fun wave => sq_nonneg _)
          (fun wave => by
            have multiplierNonneg :=
              finiteStateVorticityHeatMultiplier_nonneg
                ν.coeff duration.1 wave
            have multiplierLe :=
              finiteStateVorticityHeatMultiplier_le_one
                ν.coeff_pos.le duration.2 wave
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg multiplierNonneg]
            have normLe :
                finiteStateVorticityHeatMultiplier
                      ν.coeff duration.1 wave * ‖state wave‖ ≤
                  ‖state wave‖ := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right multiplierLe (norm_nonneg _)
            exact
              (sq_le_sq₀
                (mul_nonneg multiplierNonneg (norm_nonneg _))
                (norm_nonneg _)).2 normLe)⟩

@[simp] theorem wholeVorticityHeatEvolution_apply
    (ν : Viscosity)
    (duration : NNReal)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    wholeVorticityHeatEvolution ν duration state wave =
      finiteStateVorticityHeatMultiplier
        ν.coeff duration.1 wave • state wave :=
  rfl

/-- Homogeneous heat propagation cannot increase the complete coefficient
Hilbert norm. -/
theorem wholeVorticityHeatEvolution_norm_le
    (ν : Viscosity)
    (duration : NNReal)
    (state : ComplexVorticityHilbertState) :
    ‖wholeVorticityHeatEvolution ν duration state‖ ≤ ‖state‖ := by
  have heatSq :
      ‖wholeVorticityHeatEvolution ν duration state‖ ^ 2 ≤
        ‖state‖ ^ 2 := by
    rw [show
      ‖wholeVorticityHeatEvolution ν duration state‖ ^ 2 =
        ∑' wave : IntegerWavevector,
          ‖wholeVorticityHeatEvolution ν duration state wave‖ ^ 2 by
        simpa using
          (lp.norm_rpow_eq_tsum
            (p := (2 : ℝ≥0∞)) (by norm_num)
            (wholeVorticityHeatEvolution ν duration state))]
    rw [show
      ‖state‖ ^ 2 =
        ∑' wave : IntegerWavevector, ‖state wave‖ ^ 2 by
        simpa using
          (lp.norm_rpow_eq_tsum
            (p := (2 : ℝ≥0∞)) (by norm_num) state)]
    apply Summable.tsum_le_tsum
    · intro wave
      have multiplierNonneg :=
        finiteStateVorticityHeatMultiplier_nonneg
          ν.coeff duration.1 wave
      have multiplierLe :=
        finiteStateVorticityHeatMultiplier_le_one
          ν.coeff_pos.le duration.2 wave
      rw [wholeVorticityHeatEvolution_apply, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg multiplierNonneg]
      have normLe :
          finiteStateVorticityHeatMultiplier
                ν.coeff duration.1 wave * ‖state wave‖ ≤
            ‖state wave‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right multiplierLe (norm_nonneg _)
      exact
        (sq_le_sq₀
          (mul_nonneg multiplierNonneg (norm_nonneg _))
          (norm_nonneg _)).2 normLe
    · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        Memℓp.summable (by norm_num)
          (wholeVorticityHeatEvolution ν duration state).2
    · simpa using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞))
          (by norm_num) state).summable
  exact
    (sq_le_sq₀
      (norm_nonneg (wholeVorticityHeatEvolution ν duration state))
      (norm_nonneg state)).1 heatSq

/-! ## Actual restart regeneration -/

/-- The homogeneous heat part of the next source-generated restart edge. -/
def wholeRestartHomogeneousHeatState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ComplexVorticityHilbertState :=
  wholeVorticityHeatEvolution ν
    ⟨(run initial index).nextContact.time.1,
      (run initial index).nextContact.time_pos.le⟩
    (run initial index).contact.physicalState

@[simp] theorem wholeRestartHomogeneousHeatState_apply
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    wholeRestartHomogeneousHeatState initial index wave =
      finiteStateVorticityHeatMultiplier ν.coeff
          (run initial index).nextContact.time.1 wave •
        (run initial index).contact.physicalState wave :=
  by
    change
      finiteStateVorticityHeatMultiplier ν.coeff
          (run initial index).nextContact.time.1 wave •
        (run initial index).contact.physicalState wave = _
    rfl

/-- The actual whole-state increment regenerated beyond homogeneous heat on
one source-owned restart edge. -/
def wholeRestartNonlinearRegenerationState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ComplexVorticityHilbertState :=
  (run initial index).nextContact.physicalState -
    wholeRestartHomogeneousHeatState initial index

@[simp] theorem wholeRestartNonlinearRegenerationState_apply
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    wholeRestartNonlinearRegenerationState initial index wave =
      (run initial index).nextContact.physicalState wave -
        finiteStateVorticityHeatMultiplier ν.coeff
            (run initial index).nextContact.time.1 wave •
          (run initial index).contact.physicalState wave :=
  by
    simp [wholeRestartNonlinearRegenerationState]

/-- Every nonzero row of the whole regeneration state is exactly the
same-event nonlinear Duhamel convolution from the source-selected receipt. -/
theorem wholeRestartNonlinearRegenerationState_apply_eq_actualDuhamel
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    wholeRestartNonlinearRegenerationState initial index wave =
      receiptWeightedNonlinearDuhamelAt
        (run initial index).nextContact.prefixReceipt wave waveNonzero
        ⟨(run initial index).nextContact.time.1,
          ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ := by
  rw [wholeRestartNonlinearRegenerationState_apply]
  let current := run initial index
  let terminal : Icc (0 : ℝ) current.nextContact.time.1 :=
    ⟨current.nextContact.time.1,
      ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
  change
    current.nextContact.physicalState wave -
        finiteStateVorticityHeatMultiplier
            ν.coeff current.nextContact.time.1 wave •
          current.contact.physicalState wave =
      receiptWeightedNonlinearDuhamelAt
        current.nextContact.prefixReceipt wave waveNonzero terminal
  rw [← current.nextContact.prefixReceipt_terminal]
  exact
    wholeContinuousMildSerrinReceipt_row_sub_heat_eq
      current.nextContact.prefixReceipt wave waveNonzero terminal

/-- The complete regeneration has no hidden zero-frequency component. -/
@[simp] theorem wholeRestartNonlinearRegenerationState_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartNonlinearRegenerationState initial index 0 = 0 := by
  simp [wholeRestartNonlinearRegenerationState]

/-- Exact same-edge whole-state update: the next physical contact is heat
transport plus the generated nonlinear Duhamel remainder. -/
theorem run_contact_succ_eq_heat_add_nonlinearRegeneration
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    (run initial (index + 1)).contact.physicalState =
      wholeRestartHomogeneousHeatState initial index +
        wholeRestartNonlinearRegenerationState initial index := by
  rw [run_succ]
  change
    (run initial index).nextContact.physicalState =
      wholeRestartHomogeneousHeatState initial index +
        ((run initial index).nextContact.physicalState -
          wholeRestartHomogeneousHeatState initial index)
  abel

/-- Norm charged by the actual nonlinear regeneration on one native edge. -/
def wholeRestartNonlinearRegenerationNorm
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  ‖wholeRestartNonlinearRegenerationState initial index‖

theorem wholeRestartHomogeneousHeatState_norm_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    ‖wholeRestartHomogeneousHeatState initial index‖ ≤
      ‖(run initial index).contact.physicalState‖ :=
  wholeVorticityHeatEvolution_norm_le ν
    ⟨(run initial index).nextContact.time.1,
      (run initial index).nextContact.time_pos.le⟩
    (run initial index).contact.physicalState

/-! ## Whole-Hilbert recognition and actual block transport -/

/-- The complete physical vorticity mass at an actual contact is exactly the
squared norm of its punctured Euclidean whole-Hilbert realization. -/
theorem restartPhysicalVorticityMass_eq_puncturedEuclideanize_norm_sq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : Nat) :
    restartPhysicalVorticityMass initial index =
      ‖puncturedEuclideanize
          (run initial index).contact.physicalState‖ ^ 2 := by
  unfold restartPhysicalVorticityMass
  rw [← puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
    (run initial index).contact.physicalState
    (run initial index).contact.physicalState_zero]
  simpa [puncturedWholeVorticityEuclideanMass] using
    (puncturedEuclideanize_norm_sq
      (run initial index).contact.physicalState).symm

/-- Homogeneous whole-vorticity heat evolution preserves addition exactly. -/
theorem wholeVorticityHeatEvolution_add
    (ν : Viscosity)
    (duration : NNReal)
    (left right : ComplexVorticityHilbertState) :
    wholeVorticityHeatEvolution ν duration (left + right) =
      wholeVorticityHeatEvolution ν duration left +
        wholeVorticityHeatEvolution ν duration right := by
  apply lp.ext
  funext wave
  simp only [wholeVorticityHeatEvolution_apply]
  change
    finiteStateVorticityHeatMultiplier ν.coeff duration.1 wave •
          (left wave + right wave) =
      finiteStateVorticityHeatMultiplier ν.coeff duration.1 wave • left wave +
        finiteStateVorticityHeatMultiplier ν.coeff duration.1 wave • right wave
  exact smul_add _ _ _

/-- Heat is contractive in the complete punctured Euclidean carrier itself;
the ambient sup-row comparison constant is not paid. -/
theorem wholeVorticityHeatEvolution_punctured_norm_le
    (ν : Viscosity)
    (duration : NNReal)
    (state : ComplexVorticityHilbertState) :
    ‖puncturedEuclideanize
        (wholeVorticityHeatEvolution ν duration state)‖ ≤
      ‖puncturedEuclideanize state‖ := by
  apply lp.norm_mono (by norm_num)
  intro wave
  rw [puncturedEuclideanize_apply, puncturedEuclideanize_apply,
    wholeVorticityHeatEvolution_apply]
  have multiplierNonneg :=
    finiteStateVorticityHeatMultiplier_nonneg
      ν.coeff duration.1 wave.1
  have multiplierLe :=
    finiteStateVorticityHeatMultiplier_le_one
      ν.coeff_pos.le duration.2 wave.1
  change
    ‖finiteStateVorticityHeatMultiplier ν.coeff duration.1 wave.1 •
        euclideanCoordinateRow (state wave.1)‖ ≤
      ‖euclideanCoordinateRow (state wave.1)‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg multiplierNonneg]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right multiplierLe
      (norm_nonneg (euclideanCoordinateRow (state wave.1)))

/-- The block-start state transported through exactly `length` subsequent
native heat steps. -/
def wholeRestartBlockTransportedInitialState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start : Nat) : Nat → ComplexVorticityHilbertState
  | 0 => (run initial start).contact.physicalState
  | length + 1 =>
      wholeVorticityHeatEvolution ν
        ⟨(run initial (start + length)).nextContact.time.1,
          (run initial (start + length)).nextContact.time_pos.le⟩
        (wholeRestartBlockTransportedInitialState initial start length)

/-- The recursive homogeneous transport of the block-start row is one heat
multiplier over the difference of the two actual contact endpoint clocks. -/
theorem wholeRestartBlockTransportedInitialState_apply_eq_totalHeat
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start length : Nat)
    (wave : IntegerWavevector) :
    wholeRestartBlockTransportedInitialState initial start length wave =
      finiteStateVorticityHeatMultiplier ν.coeff
          (elapsedTime initial (start + length + 1) -
            elapsedTime initial (start + 1)) wave •
        (run initial start).contact.physicalState wave := by
  induction length with
  | zero =>
      simp [wholeRestartBlockTransportedInitialState,
        finiteStateVorticityHeatMultiplier]
  | succ length inductionHypothesis =>
      rw [wholeRestartBlockTransportedInitialState]
      change
        finiteStateVorticityHeatMultiplier ν.coeff
              (run initial (start + length)).nextContact.time.1 wave •
            wholeRestartBlockTransportedInitialState
              initial start length wave = _
      rw [inductionHypothesis, smul_smul]
      congr 1
      unfold finiteStateVorticityHeatMultiplier
      rw [← Real.exp_add]
      congr 1
      have clockStep :
          elapsedTime initial (start + (length + 1) + 1) =
            elapsedTime initial (start + length + 1) +
              (run initial (start + length)).nextContact.time.1 := by
        rw [show start + (length + 1) + 1 =
            (start + length + 1) + 1 by omega,
          elapsedTime_succ]
        congr 1
      rw [clockStep]
      ring

/-- The causal nonlinear aggregate on an actual restart block. Each earlier
remainder is transported by every later native heat step before the newest
same-edge remainder is written. -/
def wholeRestartBlockNonlinearRegenerationAggregate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start : Nat) : Nat → ComplexVorticityHilbertState
  | 0 => 0
  | length + 1 =>
      wholeVorticityHeatEvolution ν
          ⟨(run initial (start + length)).nextContact.time.1,
            (run initial (start + length)).nextContact.time_pos.le⟩
          (wholeRestartBlockNonlinearRegenerationAggregate
            initial start length) +
        wholeRestartNonlinearRegenerationState initial (start + length)

/-- Exact whole-state Duhamel recursion over an arbitrary literal block of
the authoritative native run. -/
theorem run_contact_eq_blockTransportedInitial_add_nonlinearAggregate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start : Nat) :
    ∀ length : Nat,
      (run initial (start + length)).contact.physicalState =
        wholeRestartBlockTransportedInitialState initial start length +
          wholeRestartBlockNonlinearRegenerationAggregate
            initial start length
  | 0 => by
      simp [wholeRestartBlockTransportedInitialState,
        wholeRestartBlockNonlinearRegenerationAggregate]
  | length + 1 => by
      rw [Nat.add_succ,
        run_contact_succ_eq_heat_add_nonlinearRegeneration]
      rw [wholeRestartBlockTransportedInitialState,
        wholeRestartBlockNonlinearRegenerationAggregate]
      unfold wholeRestartHomogeneousHeatState
      let duration : NNReal :=
        ⟨(run initial (start + length)).nextContact.time.1,
          (run initial (start + length)).nextContact.time_pos.le⟩
      have previous :=
        run_contact_eq_blockTransportedInitial_add_nonlinearAggregate
          initial start length
      have heatPrevious :=
        congrArg (wholeVorticityHeatEvolution ν duration) previous
      change
        wholeVorticityHeatEvolution ν duration
              (run initial (start + length)).contact.physicalState +
            wholeRestartNonlinearRegenerationState
              initial (start + length) =
          wholeVorticityHeatEvolution ν duration
                (wholeRestartBlockTransportedInitialState
                  initial start length) +
            (wholeVorticityHeatEvolution ν duration
                (wholeRestartBlockNonlinearRegenerationAggregate
                  initial start length) +
              wholeRestartNonlinearRegenerationState
                initial (start + length))
      calc
        wholeVorticityHeatEvolution ν duration
                (run initial (start + length)).contact.physicalState +
              wholeRestartNonlinearRegenerationState
                initial (start + length) =
            wholeVorticityHeatEvolution ν duration
                  (wholeRestartBlockTransportedInitialState
                      initial start length +
                    wholeRestartBlockNonlinearRegenerationAggregate
                      initial start length) +
                wholeRestartNonlinearRegenerationState
                  initial (start + length) := by
              rw [heatPrevious]
        _ =
            (wholeVorticityHeatEvolution ν duration
                (wholeRestartBlockTransportedInitialState
                  initial start length) +
              wholeVorticityHeatEvolution ν duration
                (wholeRestartBlockNonlinearRegenerationAggregate
                  initial start length)) +
                wholeRestartNonlinearRegenerationState
                  initial (start + length) := by
              rw [wholeVorticityHeatEvolution_add]
        _ =
            wholeVorticityHeatEvolution ν duration
                  (wholeRestartBlockTransportedInitialState
                    initial start length) +
              (wholeVorticityHeatEvolution ν duration
                  (wholeRestartBlockNonlinearRegenerationAggregate
                    initial start length) +
                wholeRestartNonlinearRegenerationState
                  initial (start + length)) := by
              abel

/-- The transported block-start part retains no more punctured whole-Hilbert
norm than the actual block-start state. -/
theorem blockTransportedInitial_punctured_norm_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start : Nat) :
    ∀ length : Nat,
      ‖puncturedEuclideanize
          (wholeRestartBlockTransportedInitialState
            initial start length)‖ ≤
        ‖puncturedEuclideanize
          (run initial start).contact.physicalState‖
  | 0 => by
      simp [wholeRestartBlockTransportedInitialState]
  | length + 1 =>
      (wholeVorticityHeatEvolution_punctured_norm_le ν
        ⟨(run initial (start + length)).nextContact.time.1,
          (run initial (start + length)).nextContact.time_pos.le⟩
        (wholeRestartBlockTransportedInitialState
          initial start length)).trans
        (blockTransportedInitial_punctured_norm_le initial start length)

/-! ## Path accumulation -/

/-- Every finite native prefix is bounded by the initial whole-state norm
plus the nonlinear regeneration norms actually written on that prefix. -/
theorem run_contact_norm_le_initial_add_regenerationPrefix
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : ℕ,
      ‖(run initial length).contact.physicalState‖ ≤
        ‖initial.contact.physicalState‖ +
          ∑ index ∈ Finset.range length,
            wholeRestartNonlinearRegenerationNorm initial index
  | 0 => by simp
  | length + 1 => by
      have decomposition :=
        run_contact_succ_eq_heat_add_nonlinearRegeneration
          initial length
      have heatLe :=
        wholeRestartHomogeneousHeatState_norm_le initial length
      have previousLe :=
        run_contact_norm_le_initial_add_regenerationPrefix
          initial length
      calc
        ‖(run initial (length + 1)).contact.physicalState‖ =
            ‖wholeRestartHomogeneousHeatState initial length +
              wholeRestartNonlinearRegenerationState initial length‖ := by
          rw [decomposition]
        _ ≤ ‖wholeRestartHomogeneousHeatState initial length‖ +
              ‖wholeRestartNonlinearRegenerationState initial length‖ :=
          norm_add_le _ _
        _ ≤ ‖(run initial length).contact.physicalState‖ +
              wholeRestartNonlinearRegenerationNorm initial length := by
          exact add_le_add heatLe (le_refl _)
        _ ≤
            (‖initial.contact.physicalState‖ +
                ∑ index ∈ Finset.range length,
                  wholeRestartNonlinearRegenerationNorm initial index) +
              wholeRestartNonlinearRegenerationNorm initial length := by
          exact add_le_add previousLe (le_refl _)
        _ = ‖initial.contact.physicalState‖ +
              ∑ index ∈ Finset.range (length + 1),
                wholeRestartNonlinearRegenerationNorm initial index := by
          rw [Finset.sum_range_succ]
          ring

/-- Summable actual nonlinear regeneration would uniformly bound all whole
physical contact states on the native restart chain. -/
theorem run_contact_norm_bddAbove_of_regenerationNorm_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (regenerationSummable :
      Summable
        (wholeRestartNonlinearRegenerationNorm initial)) :
    BddAbove
      (Set.range fun index =>
        ‖(run initial index).contact.physicalState‖) := by
  refine
    ⟨‖initial.contact.physicalState‖ +
        ∑' index, wholeRestartNonlinearRegenerationNorm initial index,
      ?_⟩
  rintro _ ⟨length, rfl⟩
  calc
    ‖(run initial length).contact.physicalState‖ ≤
        ‖initial.contact.physicalState‖ +
          ∑ index ∈ Finset.range length,
            wholeRestartNonlinearRegenerationNorm initial index :=
      run_contact_norm_le_initial_add_regenerationPrefix initial length
    _ ≤
        ‖initial.contact.physicalState‖ +
          ∑' index,
            wholeRestartNonlinearRegenerationNorm initial index := by
      gcongr
      exact regenerationSummable.sum_le_tsum
        (Finset.range length)
        (fun index indexMem => norm_nonneg _)

/-- A uniform Hilbert-norm bound on generated contact states would bound the
whole Euclidean coefficient mass used by the finite-time obstruction. -/
theorem restartPhysicalVorticityMass_bddAbove_of_contact_norm_bddAbove
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (contactNormBounded :
      BddAbove
        (Set.range fun index =>
          ‖(run initial index).contact.physicalState‖)) :
    BddAbove
      (Set.range (restartPhysicalVorticityMass initial)) := by
  rcases contactNormBounded with ⟨upper, upperBound⟩
  refine ⟨3 * (max upper 0) ^ 2, ?_⟩
  rintro _ ⟨index, rfl⟩
  have normLe :
      ‖(run initial index).contact.physicalState‖ ≤ max upper 0 :=
    (upperBound ⟨index, rfl⟩).trans (le_max_left upper 0)
  calc
    restartPhysicalVorticityMass initial index =
        wholeVorticityEuclideanMass
          (run initial index).contact.physicalState := rfl
    _ ≤ 3 * ‖(run initial index).contact.physicalState‖ ^ 2 :=
      wholeVorticityEuclideanMass_le_three_mul_norm_sq _
    _ ≤ 3 * (max upper 0) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (le_max_right upper 0)).2 normLe)
        (by norm_num)

/-- Main hard-gate reduction: if the actual native whole-flow restart chain
accumulates in finite physical time, its same-event nonlinear Duhamel
regeneration norms cannot be summable.  Homogeneous heat propagation is not
charged as a new responsibility. -/
theorem elapsedTime_bddAbove_forces_nonlinearRegenerationNorm_not_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))) :
    ¬ Summable
      (wholeRestartNonlinearRegenerationNorm initial) := by
  intro regenerationSummable
  have contactNormBounded :=
    run_contact_norm_bddAbove_of_regenerationNorm_summable
      initial regenerationSummable
  have physicalMassBounded :=
    restartPhysicalVorticityMass_bddAbove_of_contact_norm_bddAbove
      initial contactNormBounded
  exact
    (elapsedTime_bddAbove_forces_physicalVorticityMass_unbounded
      initial elapsedBounded) physicalMassBounded

/-- Premise-free exhaustion on the actual native recursion: either generated
physical time is unbounded, or the nonlinear regeneration norms written by
the same restart edges are not summable. -/
theorem elapsedTime_unbounded_or_nonlinearRegenerationNorm_not_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ¬ BddAbove (Set.range (elapsedTime initial)) ∨
      ¬ Summable
        (wholeRestartNonlinearRegenerationNorm initial) := by
  by_cases elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))
  · exact Or.inr
      (elapsedTime_bddAbove_forces_nonlinearRegenerationNorm_not_summable
        initial elapsedBounded)
  · exact Or.inl elapsedBounded

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
end NavierStokes
end SaturationMonoid
