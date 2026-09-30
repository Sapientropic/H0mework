import H0mework.Versions.X.Fock.CopyGraph.TemporalAcquisitionSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedJointTime SourceGeneratedActionWords.Fock.OriginalHilbert SourceSuccessorBoundary
noncomputable section

theorem next_word_outside (depth bound : Nat) (value : NextSpace depth bound) (coordinate : Nat)
    (outside : bound + 2 ≤ coordinate) : nextWord depth bound value coordinate = 0 := by
  rw [next_word_is_source_push]
  cases coordinate with
  | zero => omega
  | succ coordinate =>
    change Finsupp.mapDomain Nat.succ (SourceHistoryWord.word bound (Actor.nextPullback depth bound value)) (coordinate + 1) = 0
    rw [Finsupp.mapDomain_apply Nat.succ_injective]
    exact SourceHistoryWord.word_outside bound _ coordinate (by omega)

def nextField (depth bound : Nat) (value : NextSpace depth bound) : FieldSpace (bound + 1) (bound + 1) :=
  Actor.currentTransfer (bound + 1) (bound + 1) (SourceHistoryWord.lift (bound + 1) (nextWord depth bound value))

theorem next_field_word (depth bound : Nat) (value : NextSpace depth bound) :
    word (bound + 1) (bound + 1) (nextField depth bound value) = nextWord depth bound value := by
  rw [nextField, word_from_actor]
  apply SourceHistoryWord.word_lift
  intro coordinate present
  by_contra outside
  have zero := next_word_outside depth bound value coordinate (by omega)
  exact (Finsupp.mem_support_iff.mp present) zero

theorem next_field_read (depth bound : Nat) (value : NextSpace depth bound) :
    fieldRead (bound + 1) (bound + 1) (nextField depth bound value) = nextFieldRead depth bound value := by
  change SourceJointClockGraph.read (word (bound + 1) (bound + 1) (nextField depth bound value)) =
    SourceJointClockGraph.read (nextWord depth bound value)
  rw [next_field_word]

def timeField (depth bound : Nat) (value : FieldSpace depth bound) : FieldSpace (bound + 1) (bound + 1) :=
  nextField depth bound (timeTransfer depth bound value)

theorem time_field_read (depth bound : Nat) (value : FieldSpace depth bound) :
    fieldRead (bound + 1) (bound + 1) (timeField depth bound value) =
      SourceJointClockGraph.action (fieldRead depth bound value) := by
  rw [timeField, next_field_read, original_time_square]

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
