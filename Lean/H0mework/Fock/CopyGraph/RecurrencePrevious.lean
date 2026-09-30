import H0mework.Fock.CopyGraph.FibreObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def observedFromPrevious (depth : Nat) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) :
    SourceJointClockGraph.Carrier →L[ℂ] Space (observed (historyPMF depth) (oldRead depth read)) :=
  (transfer (historyPMF depth) (oldRead depth read)).comp ((Actor.currentPullback depth depth).toContinuousLinearMap.comp previous)

theorem observed_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    observedFromPrevious depth read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) =
      SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) := by
  apply ContinuousLinearMap.ext
  intro value
  change transfer (historyPMF depth) (oldRead depth read)
    (Actor.currentPullback depth depth (SourceConditionalGraphDecoder.realizeObserved depth depth (oldRead depth read)
      (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) value))) = _
  rw [SourceConditionalGraphDecoder.realized_samples, IsometricRetainedTransfer.transfer_pullback]

def predictionFromPrevious (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (SourceGraphGrowth.oldAction depth index read).comp (observedFromPrevious depth read previous)

def innovationFromPrevious (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) : SourceJointClockGraph.Carrier :=
  SourceGraphBirth.fresh depth index - predictionFromPrevious depth index read previous (SourceGraphBirth.fresh depth index)

theorem innovation_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    innovationFromPrevious depth index read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) =
      SourceGraphBirth.innovation depth index read := by
  rw [innovationFromPrevious, predictionFromPrevious, observed_canonical]
  have original := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) (SourceGraphBirth.fresh depth index)
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
