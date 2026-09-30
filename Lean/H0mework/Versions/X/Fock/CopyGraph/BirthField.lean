import H0mework.Versions.X.Fock.CopyGraph.BirthEquation
import H0mework.Versions.X.Fock.CopyGraph.BirthRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAtomicObservation
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead taggedRead)
open SourceConditionalGraphDecoder (fieldDecode)
noncomputable section

abbrev freshField (depth : Nat) : FieldSpace (depth + 1) (depth + 1) :=
  Actor.currentTransfer (depth + 1) (depth + 1) (cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)))

theorem fresh_field_source (depth : Nat) (index : Index depth) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (freshField depth)) = fresh depth index :=
  SourceConditionalGraph.copy_transferred (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) _

universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def innovationField (depth : Nat) (index : Index depth) (read : Nat → Observed) : FieldSpace (depth + 1) (depth + 1) :=
  freshField depth - normalize depth (depth + 1) (Nat.le_succ depth)
    (fieldDecode depth depth index (oldRead depth read) (fresh depth index))

omit [MeasurableSingletonClass Observed] in
theorem innovation_field_source (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (innovationField depth index read)) = innovation depth index read := by
  rw [innovationField, map_sub, map_sub, fresh_field_source, SourceGraphGrowth.field_retained_target]
  have original := SourceConditionalGraphDecoder.original_reconstruction depth depth index (oldRead depth read) (fresh depth index)
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

theorem original_birth_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    SourceGraphGrowth.birthField depth index read value =
      (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovationField depth index read := by
  apply (Actor.currentPullback (depth + 1) (depth + 1)).injective
  apply copy_read_injective (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
  change SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (fieldRead (depth + 1) (depth + 1) (SourceGraphGrowth.birthField depth index read value)) =
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1)
        ((inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovationField depth index read))
  rw [← SourceGraphGrowth.birth_original, map_smul, map_smul, innovation_field_source, birth_formula]

theorem fresh_field_recovery (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) (fresh depth index) = freshField depth := by
  have original := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) (fresh depth index)
  change _ + SourceGraphGrowth.taggedResidual depth index read (fresh depth index) = fresh depth index at original
  rw [fresh_tagged_recovery, add_zero] at original
  change Actor.currentTransfer (depth + 1) (depth + 1)
    (SourceWeightedRecovery.pullback (historyPMF (depth + 1)) (taggedRead depth read)
      (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) (fresh depth index))) =
    Actor.currentTransfer (depth + 1) (depth + 1) (cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)))
  apply congrArg (Actor.currentTransfer (depth + 1) (depth + 1))
  apply copy_read_injective (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
  rw [← SourceConditionalGraphDecoder.action_source]
  exact original

theorem original_birth_realization (round depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    let gained := (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovationField depth index read
    let copied := SourceCopyGraph.complexAction (depth + 1) (FamilyModel.Fock.oldIndex depth index) (word (depth + 1) (depth + 1) gained)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        SourceGraphGrowth.birthGain depth index read value := by
  have original := SourceGraphGrowth.birth_realization round depth index read value
  rw [original_birth_formula] at original
  exact original

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
