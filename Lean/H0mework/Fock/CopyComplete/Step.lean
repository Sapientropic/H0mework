import H0mework.Fock.CopyComplete.Growth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead)
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

def step (model depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace (depth + 1) (depth + 1) :=
  let h := SourceGraphRecurrence.innovationFromPrevious depth index (read model) previous
  (normalize depth (depth + 1) (Nat.le_succ depth)).comp previous +
    (((‖h‖ ^ 2 : ℝ) : ℂ)⁻¹) •
      InnerProductSpace.rankOne ℂ (SourceGraphRecurrence.innovationField depth index previous) h

theorem step_is_original (model depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) :
    step model depth index previous = SourceGraphRecurrence.step depth index (read model) previous := by
  have absent : read model (depth + 1) ∉ (observed (historyPMF depth) (oldRead depth (read model))).support :=
    fun supported => newest_novel model depth ((atoms_iff _ _ _).mpr supported)
  rw [SourceGraphRecurrence.step, dif_neg absent, sub_zero]
  rfl

theorem step_canonical (model depth : Nat) (index : Index depth) :
    step model depth index (SourceConditionalGraphDecoder.fieldDecode depth depth index (Hilbert.read model depth)) =
      SourceConditionalGraphDecoder.fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
        (Hilbert.read model (depth + 1)) := by
  rw [step_is_original, ← old_read_original, SourceGraphRecurrence.step_canonical, new_read_original]

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
