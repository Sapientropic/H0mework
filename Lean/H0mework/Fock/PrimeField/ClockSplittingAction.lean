import H0mework.Fock.PrimeField.ClockSplittingChart

/-! The original completed action keeps the whole prime carrier and pays the clock increment from its source mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual
open SourceGeneratedScalarCofinalTopology.NativeProbability
open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem projection_action (value : JointField) :
    primeProjection (fieldAction (process := process) jointRead value) =
      fieldAction (process := process) rawField (primeProjection value) := by
  apply Limits.Concrete.limit_ext (primeData.quotientTower primeLaws)
  intro stage
  apply primeData.stageRealization_injective stage.unop
  change stageRead nativeAction observation stage.unop (primeProjection (fieldAction (process := process) jointRead value)) =
    stageRead nativeAction observation stage.unop (fieldAction (process := process) rawField (primeProjection value))
  have jointShift : stageRead nativeAction jointObservation stage.unop (fieldAction (process := process) jointRead value) =
      dropFirst (R := ℤ) stage.unop (stageRead nativeAction jointObservation (stage.unop + 1) value) :=
    endomorphism_reads_dropFirst nativeAction jointObservation stage.unop value
  have primeShift : stageRead nativeAction observation stage.unop (fieldAction (process := process) rawField (primeProjection value)) =
      dropFirst (R := ℤ) stage.unop (stageRead nativeAction observation (stage.unop + 1) (primeProjection value)) :=
    endomorphism_reads_dropFirst nativeAction observation stage.unop (primeProjection value)
  rw [projection_prefix, jointShift, primeShift, projection_prefix]
  rfl

theorem clock_action (value : JointField) :
    clockRead (fieldAction (process := process) jointRead value) =
      clockRead value + SourcePrimeCompletion.mass (primeProjection value) := by
  have shifted : stageRead nativeAction jointObservation 0 (fieldAction (process := process) jointRead value) =
      dropFirst (R := ℤ) 0 (stageRead nativeAction jointObservation 1 value) :=
    endomorphism_reads_dropFirst nativeAction jointObservation 0 value
  have readClock := congrArg (fun reads => (reads (0 : Fin 1)).2) shifted
  change clockRead (fieldAction (process := process) jointRead value) = clockAt 1 value at readClock
  exact readClock.trans (by simpa only [Nat.cast_one, one_mul] using clock_law value 1)

theorem action_equation (value : JointField) :
    coordinates (fieldAction (process := process) jointRead value) =
      (fieldAction (process := process) rawField (primeProjection value),
        clockRead value + SourcePrimeCompletion.mass (primeProjection value)) :=
  Prod.ext (projection_action value) (clock_action value)

theorem action_on_rebuild (value : SourcePrimeCompletion.Field) (clock : ℤ) :
    fieldAction (process := process) jointRead (rebuild (value, clock)) =
      rebuild (fieldAction (process := process) rawField value, clock + SourcePrimeCompletion.mass value) := by
  apply joint_ext
  · rw [projection_action, rebuild_prime, rebuild_prime]
  · rw [clock_action, rebuild_clock, rebuild_prime, rebuild_clock]

theorem clock_zero_section_defect (value : SourcePrimeCompletion.Field) :
    clockRead (fieldAction (process := process) jointRead (sectionMap value)) = SourcePrimeCompletion.mass value := by
  rw [clock_action, section_clock, section_prime, zero_add]

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
