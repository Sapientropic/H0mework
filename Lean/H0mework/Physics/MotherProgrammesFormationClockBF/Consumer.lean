import H0mework.Physics.MotherProgrammesFormationClockBF.Preparation
import H0mework.Physics.MotherProgrammesFormationClockBF.Split
import H0mework.Physics.MotherProgrammesFormationClockBF.Calculus

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFConsumer

open StageNineHolonomicField StageNineDiracDualFormNativeMotherAction
open Stage9C.Revision
open ClockBF ClockBFPreparation ClockBFCoordinates ClockBFSplit

noncomputable section

def encodedAt (u : ℝ) (positive : 0 < 1 + u) (step : ℕ) : (ℝ × ℝ) × Remainder :=
  wholeSplit (NativeFamily.stateAt (prepared u positive) step).current

theorem initial_encoded (u : ℝ) (positive : 0 < 1 + u) :
    encodedAt u positive 0 = ((u, 0), ⟨Runtime.configuration, read_original⟩) := by
  change wholeSplit (prepared u positive).current = _
  rw [prepared_current, generated_hidden_zero]

/-- The actual old constitutive writer minimizes the complete local density
on the generated B fibre; no minimizer is an input to the writer. -/
theorem preparation_minimizes (u b : ℝ) (positive : 0 < 1 + u) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource 0 0
        (toContinuumPointField (prepared u positive).current 0) ≤ clockBFAction u b := by
  rw [prepared_action, action_elimination u b positive]
  have square : 0 ≤ responseScale * (1 + u) * (b - generatedB u)^2 :=
    mul_nonneg (le_of_lt (mul_pos responseScale_pos positive)) (sq_nonneg _)
  linarith

theorem preparation_optimum_iff (u b : ℝ) (positive : 0 < 1 + u) :
    clockBFAction u b = sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource 0 0
        (toContinuumPointField (prepared u positive).current 0) ↔ b = generatedB u := by
  rw [prepared_action]
  exact generatedB_unique u b positive

theorem preparation_exact_effect (u : ℝ) (positive : 0 < 1 + u) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource 0 0
        (toContinuumPointField
          (wholeSplit.symm (encodedAt u positive 0)) 0) = effectiveClockAction u := by
  change sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource 0 0
      (toContinuumPointField (wholeSplit.symm (wholeSplit (prepared u positive).current)) 0) = _
  rw [wholeSplit.symm_apply_apply]
  exact prepared_action u positive

/-- The native writer keeps the entire coframe field, including its physical
clock column, at every generated local visit. -/
theorem generated_coframe (u : ℝ) (positive : 0 < 1 + u) (step : ℕ) :
    (NativeFamily.stateAt (prepared u positive) step).current.coframe =
      (clockBFConfiguration u (generatedB u)).coframe := by
  induction step with
  | zero =>
    change (prepared u positive).current.coframe = _
    rw [prepared_current]
  | succ step previous => exact previous

theorem generated_clock (u : ℝ) (positive : 0 < 1 + u) (step : ℕ) :
    (encodedAt u positive step).1.1 = u := by
  change (read (NativeFamily.stateAt (prepared u positive) step).current).1 = u
  have clock := congrArg (fun field => field 0 0 0) (generated_coframe u positive step)
  change (NativeFamily.stateAt (prepared u positive) step).current.coframe 0 0 0 /
    ClockBFMaterial.origin.coframe 0 0 - 1 = u
  rw [clock]
  change (read (clockBFConfiguration u (generatedB u))).1 = u
  rw [configuration_eq_displace, source_displacement_read]

/-- Recover the complete field read at each exact original-law visit.
The visit itself retains its source-owned history. -/
theorem generated_field_recovery (u : ℝ) (positive : 0 < 1 + u) (step : ℕ) :
    wholeSplit.symm (encodedAt u positive step) =
      (NativeFamily.stateAt (prepared u positive) step).current :=
  wholeSplit.symm_apply_apply _

set_option maxHeartbeats 2000000 in
/-- The next encoded field is the actual original compiler output, with its
complete patch and original source successor, not an independent local law. -/
theorem native_encoded_next (u : ℝ) (positive : 0 < 1 + u) (step : ℕ) :
    let current := NativeFamily.stateAt (prepared u positive) step
    let event := NativeFamily.occurrenceAt (prepared u positive) step
    let successor := NativeFamily.successorAt (prepared u positive) step
    SpinPair.source.toRootSource.actual.compile event =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running current))) ∧
    successor.targetCurrent = (NativeFamily.visitAt (prepared u positive) (step + 1)).current ∧
    wholeSplit.symm (encodedAt u positive (step + 1)) =
      Recognition.wholeField successor.targetCurrent ∧
    (encodedAt u positive (step + 1)).1.1 = u ∧
    successor.ledgerEvolution = (SpinPair.generatedPatch event).toLedgerWriteEvolution := by
  obtain ⟨compiled, next, _, _⟩ := native_consumed u positive step
  refine ⟨compiled, next, ?_, generated_clock u positive (step + 1),
    NativeFamily.complete_patch_consumed (prepared u positive) step⟩
  rw [next, generated_field_recovery]
  rfl

/-- The original complete field is itself the generated zero-clock member. -/
theorem original_member : (prepared 0 (by norm_num)).current = Runtime.configuration := by
  rw [prepared_current]
  simpa [generatedB] using original_configuration

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFConsumer
