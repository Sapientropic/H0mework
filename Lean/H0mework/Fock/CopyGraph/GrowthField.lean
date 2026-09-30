import H0mework.Fock.CopyGraph.GrowthBalance
import H0mework.Fock.CopyGraph.RefinementField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceOwnedObservationHistory
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (fieldDecode)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem field_retained_target (depth : Nat) (index : Index depth) (value : FieldSpace depth depth) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (normalize depth (depth + 1) (Nat.le_succ depth) value)) =
        SourceCopyGraph.action depth index (fieldRead depth depth value) := by
  change SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (SourceJointClockGraph.read (word (depth + 1) (depth + 1) (normalize depth (depth + 1) (Nat.le_succ depth) value))) =
    SourceCopyGraph.action depth index (SourceJointClockGraph.read (word depth depth value))
  rw [normalize_word, SourceCopyGraph.action_source, SourceCopyGraph.action_source, old_complex_action]

theorem tagged_field_recovery (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)
      (oldAction depth index read value) =
        normalize depth (depth + 1) (Nat.le_succ depth)
          (SourceConditionalGraphDecoder.realizeObserved depth depth (oldRead depth read) value) := by
  rw [← retained_action depth index read value]
  change SourceGeneratedActionWords.Fock.OriginalHilbert.Actor.currentTransfer (depth + 1) (depth + 1)
    (pullback (historyPMF (depth + 1)) (taggedRead depth read)
      (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)
        (taggedAction depth index read (retainedLift depth read value)))) = _
  rw [SourceConditionalGraphDecoder.decode_action, retained_lift_source]
  unfold SourceGeneratedAcquisitionJoint.normalize
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [SourceConditionalGraphDecoder.realized_samples]

def birthField (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) : FieldSpace (depth + 1) (depth + 1) :=
  fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value -
    normalize depth (depth + 1) (Nat.le_succ depth) (fieldDecode depth depth index (oldRead depth read) value)

def forgettingField (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) : FieldSpace (depth + 1) (depth + 1) :=
  fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value -
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value

omit [MeasurableSingletonClass Observed] in
theorem birth_original (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    birthGain depth index read value =
      SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
        (fieldRead (depth + 1) (depth + 1) (birthField depth index read value)) := by
  rw [birthField, map_sub, map_sub, field_retained_target]
  change taggedAction depth index read (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value) -
      oldAction depth index read (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) value) = _
  simp only [fieldDecode, ContinuousLinearMap.comp_apply]
  rw [SourceConditionalGraphDecoder.realized_action, SourceConditionalGraphDecoder.realized_action]

omit [MeasurableSingletonClass Observed] in
theorem forgetting_original (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    forgettingLoss depth index read value =
      SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
        (fieldRead (depth + 1) (depth + 1) (forgettingField depth index read value)) := by
  have original := SourceGraphRefinement.gain_original (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) Prod.fst value
  simpa only [forgettingLoss, forgettingField, tagged_forget] using original

omit [MeasurableSingletonClass Observed] in
theorem new_original_residual (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : FieldSpace depth depth) :
    let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
    newResidual depth index read target =
      SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
        (fieldRead (depth + 1) (depth + 1) (normalize depth (depth + 1) (Nat.le_succ depth) value -
          fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) target)) := by
  have original := SourceConditionalGraphDecoder.original_residual (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (newRead depth read) (normalize depth (depth + 1) (Nat.le_succ depth) value)
  rw [field_retained_target] at original
  exact original

theorem original_growth_budget (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : FieldSpace depth depth) :
    let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
    let freshIndex := FamilyModel.Fock.oldIndex depth index
    ‖SourceCopyGraph.action (depth + 1) freshIndex (fieldRead (depth + 1) (depth + 1)
      (normalize depth (depth + 1) (Nat.le_succ depth) value - fieldDecode (depth + 1) (depth + 1) freshIndex (newRead depth read) target))‖ ^ 2 +
      ‖SourceCopyGraph.action (depth + 1) freshIndex (fieldRead (depth + 1) (depth + 1) (birthField depth index read target))‖ ^ 2 =
    ‖SourceCopyGraph.action depth index (fieldRead depth depth (value - fieldDecode depth depth index (oldRead depth read) target))‖ ^ 2 +
      ‖SourceCopyGraph.action (depth + 1) freshIndex (fieldRead (depth + 1) (depth + 1) (forgettingField depth index read target))‖ ^ 2 := by
  have generated := growth_energy depth index read (SourceCopyGraph.action depth index (fieldRead depth depth value))
  rw [new_original_residual, birth_original, forgetting_original] at generated
  unfold oldResidual at generated
  rw [SourceConditionalGraphDecoder.original_residual] at generated
  exact generated

omit [MeasurableSingletonClass Observed] in
theorem birth_realization (round depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    let copied := SourceCopyGraph.complexAction (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (word (depth + 1) (depth + 1) (birthField depth index read value))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        birthGain depth index read value :=
  (SourceCopyGraph.original_copy_realization round (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) _).trans
    (birth_original depth index read value).symm

omit [MeasurableSingletonClass Observed] in
theorem forgetting_realization (round depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    let copied := SourceCopyGraph.complexAction (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (word (depth + 1) (depth + 1) (forgettingField depth index read value))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        forgettingLoss depth index read value :=
  (SourceCopyGraph.original_copy_realization round (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) _).trans
    (forgetting_original depth index read value).symm

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
