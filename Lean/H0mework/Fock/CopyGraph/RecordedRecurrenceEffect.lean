import H0mework.Fock.CopyGraph.RecordedRecurrencePrediction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecordedRecurrence

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem time_add (left right : Nat) (target : SourceJointClockGraph.Carrier) :
    time left (time right target) = time (left + right) target := by
  change (SourceJointClockGraph.action ^ left * SourceJointClockGraph.action ^ right) target =
    (SourceJointClockGraph.action ^ (left + right)) target
  rw [pow_add]

theorem time_commute (left right : Nat) (target : SourceJointClockGraph.Carrier) :
    time left (time right target) = time right (time left target) := by
  rw [time_add, time_add, Nat.add_comm left right]

theorem difference_time (stage ticks : Nat) (target : SourceJointClockGraph.Carrier) :
    time ticks (difference stage target) = difference stage (time ticks target) := by
  simp only [difference, map_add, map_sub, map_smul, time_commute ticks]

def hidden (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) : SourceJointClockGraph.Carrier :=
  difference (cutoff runtime index steps + 1) (SourceJointClockGraph.read (Finsupp.single 0 (1 : ℂ)))

theorem hidden_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    hidden runtime index steps = SourceJointClockGraph.read
      (Finsupp.single (cutoff runtime index steps + 1 + 2) (1 : ℂ) -
        (2 : ℂ) • Finsupp.single (cutoff runtime index steps + 1 + 1) (1 : ℂ) +
        Finsupp.single (cutoff runtime index steps + 1) (1 : ℂ)) := by
  simp only [hidden, difference, SourceCopyTemporalAcquisition.time_word_read,
    Finsupp.mapDomain_single, Nat.zero_add, map_add, map_sub, map_smul]

theorem hidden_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    hilbert (hidden runtime index steps) (cutoff runtime index steps + 1) = 1 := by
  rw [hidden_source]
  change readWord _ (cutoff runtime index steps + 1) = 1
  rw [readWord_coordinate]
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (show cutoff runtime index steps + 1 ≠ cutoff runtime index steps + 1 + 2 by omega),
    Finsupp.single_eq_of_ne (show cutoff runtime index steps + 1 ≠ cutoff runtime index steps + 1 + 1 by omega)]
  ring

theorem hidden_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    hidden runtime index steps ≠ 0 := by
  intro zero
  have source := hidden_coordinate runtime index steps
  rw [zero] at source
  change (0 : ℂ) = 1 at source
  exact zero_ne_one source

theorem hidden_future_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat) :
    observer runtime index steps (time ticks (hidden runtime index steps)) = 0 := by
  rw [hidden, difference_time]
  exact observer_difference_zero runtime index steps _

theorem hidden_same_window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    recordedPrefix runtime index steps (windowBound runtime index steps) (hidden runtime index steps) =
      recordedPrefix runtime index steps (windowBound runtime index steps) 0 := by
  apply (model_fibre runtime index steps _ _).mpr
  intro ticks
  rw [hidden_future_zero, map_zero, map_zero]

theorem no_source_decoder (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ¬ ∃ recover : SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier (windowBound runtime index steps) →
        SourceJointClockGraph.Carrier,
      ∀ target, recover (recordedPrefix runtime index steps (windowBound runtime index steps) target) = target := by
  rintro ⟨recover, exactSource⟩
  have same := congrArg recover (hidden_same_window runtime index steps)
  rw [exactSource, exactSource] at same
  exact hidden_nonzero runtime index steps same

end
end SourceCopyRecordedRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
