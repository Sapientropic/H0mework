import H0mework.Fock.CopyGraph.TemporalAcquisitionField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceCopyProgram (Index scale indexAfter)
open SourceCopyTimeModel (time)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceSuccessorBoundary
noncomputable section

theorem time_word_read (steps : Nat) (sourceWord : Nat →₀ ℂ) :
    time steps (SourceJointClockGraph.read sourceWord) =
      SourceJointClockGraph.read (Finsupp.mapDomain (fun coordinate => coordinate + steps) sourceWord) := by
  induction steps with
  | zero =>
    change SourceJointClockGraph.read sourceWord = SourceJointClockGraph.read (Finsupp.mapDomain id sourceWord)
    rw [Finsupp.mapDomain_id]
  | succ steps previous =>
    rw [SourceCopyTimeModel.time_succ, previous, SourceJointClockGraph.action_source]
    change SourceJointClockGraph.read (Finsupp.mapDomain Nat.succ
      (Finsupp.mapDomain (fun coordinate => coordinate + steps) sourceWord)) = _
    rw [← Finsupp.mapDomain_comp]
    rfl

theorem copy_time_word (depth : Nat) (index : Index depth) (sourceWord : Nat →₀ ℂ) :
    time (scale depth index) (SourceCopyGraph.action depth index (SourceJointClockGraph.read sourceWord)) =
      SourceCopyGraph.action depth index (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)) := by
  rw [SourceCopyGraph.action_source, time_word_read, SourceJointClockGraph.action_source, SourceCopyGraph.action_source]
  change SourceJointClockGraph.read (Finsupp.mapDomain (fun coordinate => coordinate + scale depth index)
    (Finsupp.mapDomain (indexAfter depth index) sourceWord)) =
    SourceJointClockGraph.read (Finsupp.mapDomain (indexAfter depth index) (Finsupp.mapDomain Nat.succ sourceWord))
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  have addresses : (fun coordinate => indexAfter depth index coordinate + scale depth index) =
      (fun coordinate => indexAfter depth index (coordinate + 1)) := by
    funext coordinate
    exact (SourceCopyTimeModel.index_successor depth index coordinate).symm
  exact congrArg (fun address => SourceJointClockGraph.read (Finsupp.mapDomain address sourceWord)) addresses

theorem copy_time_field (depth bound : Nat) (index : Index depth) (value : FieldSpace bound bound) :
    time (scale depth index) (SourceCopyGraph.action depth index (fieldRead bound bound value)) =
      SourceCopyGraph.action depth index (fieldRead (bound + 1) (bound + 1) (timeField bound bound value)) := by
  rw [time_field_read]
  exact copy_time_word depth index (word bound bound value)

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
