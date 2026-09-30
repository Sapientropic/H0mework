import H0mework.Versions.X.Fock.PrimeField.ClockSplittingSource

/-! The full chart reads the original raw query and its original conditional transfer at the same actual next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalTransfer SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

def rawRead (value : SourcePrimeCompletion.Field × ℤ) : Raw :=
  fun _ => (SourcePrimeCompletion.read 0 value.1, value.2)

theorem raw_read_coordinates (value : JointField) :
    rawRead (coordinates value) = stageRead nativeAction jointObservation 0 value := by
  funext index
  have indexZero : index = 0 := Fin.eq_zero index
  subst index
  apply Prod.ext
  · change SourcePrimeCompletion.read 0 (primeProjection value) = (stageRead nativeAction jointObservation 0 value 0).1
    change stageRead nativeAction observation 0 (primeProjection value) 0 = _
    rw [projection_prefix]
  · rfl

theorem actual_query_from_chart (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    rawRead (coordinates (nextAtom (process := process) jointRead current bound actor)) = observe current bound actor := by
  rw [raw_read_coordinates]
  exact FiniteRecurrence.Native.fieldRead_query (process := process) jointRead 0 current bound actor

theorem chart_restores_model (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    restoredModel (rawRead (coordinates (nextAtom (process := process) jointRead current bound actor))) =
      SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock (current.advance actor.val) := by
  rw [actual_query_from_chart]
  exact restored_model_actual current bound actor

theorem original_transfer_from_chart (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField current bound
      (Runtime.Actor.actorTransfer (process := process) rawField current bound
        (taskValue (historyPMF bound) (fun index => (sample current bound index : Nat))))
      (primeProjection (nextAtom (process := process) jointRead current bound actor)) =
        decodeClock (rawRead (coordinates (nextAtom (process := process) jointRead current bound actor))) := by
  rw [actual_query_from_chart]
  exact projected_transfer_recovers current bound actor

theorem native_prime_mass (current : LivingRuntimeState process) :
    SourcePrimeCompletion.mass (fieldPoint (process := process) rawField current.state) = 1 :=
  (SourcePrimeCompletion.mass_source (SourceOperationNative.point current)).trans
    (SourceSuccessorBoundary.mass_single ℤ current.state 1)

theorem native_action_equation (current : LivingRuntimeState process) :
    coordinates (fieldPoint (process := process) jointRead current.tick.next.state) =
      (fieldAction (process := process) rawField (fieldPoint (process := process) rawField current.state),
        SourceClockModel.rawClock current.state + 1) := by
  have source := action_equation (fieldPoint (process := process) jointRead current.state)
  have first := congrArg Prod.fst (native_coordinates current)
  have second := congrArg Prod.snd (native_coordinates current)
  change primeProjection (fieldPoint (process := process) jointRead current.state) =
    fieldPoint (process := process) rawField current.state at first
  change clockRead (fieldPoint (process := process) jointRead current.state) = SourceClockModel.rawClock current.state at second
  rw [first, second, native_prime_mass] at source
  exact (congrArg coordinates (fieldPoint_action (process := process) jointRead current.state)).symm.trans source

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
