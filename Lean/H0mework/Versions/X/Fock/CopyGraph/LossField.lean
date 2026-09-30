import H0mework.Versions.X.Fock.CopyGraph.LossEquation
import H0mework.Versions.X.Fock.CopyGraph.LossRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead taggedRead)
open SourceConditionalGraphDecoder (fieldDecode)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def directionField (depth : Nat) (index : Index depth) (read : Nat → Observed) : FieldSpace (depth + 1) (depth + 1) :=
  SourceGraphGrowth.forgettingField depth index read (SourceGraphBirth.fresh depth index)

theorem direction_field_source (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (directionField depth index read)) = direction depth index read :=
  (SourceGraphGrowth.forgetting_original depth index read (SourceGraphBirth.fresh depth index)).symm.trans
    (fresh_loss depth index read)

theorem original_loss_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    SourceGraphGrowth.forgettingField depth index read value =
      (inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • directionField depth index read := by
  apply (Actor.currentPullback (depth + 1) (depth + 1)).injective
  apply SourceGraphBirth.copy_read_injective (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
  change SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (fieldRead (depth + 1) (depth + 1) (SourceGraphGrowth.forgettingField depth index read value)) =
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1)
        ((inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • directionField depth index read))
  rw [← SourceGraphGrowth.forgetting_original, map_smul, map_smul, direction_field_source, loss_formula]

theorem raw_field_update (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value =
      fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value -
        (inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • directionField depth index read := by
  have generated := original_loss_formula depth index read value
  unfold SourceGraphGrowth.forgettingField at generated
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp generated).symm)

theorem whole_field_update (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value =
      normalize depth (depth + 1) (Nat.le_succ depth) (fieldDecode depth depth index (oldRead depth read) value) +
        (inner ℂ (SourceGraphBirth.innovation depth index read) value / ((‖SourceGraphBirth.innovation depth index read‖ ^ 2 : ℝ) : ℂ)) •
          SourceGraphBirth.innovationField depth index read -
        (inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • directionField depth index read := by
  rw [raw_field_update, SourceGraphBirth.field_decoder_update]

theorem original_loss_realization (round depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    let lost := (inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • directionField depth index read
    let copied := SourceCopyGraph.complexAction (depth + 1) (FamilyModel.Fock.oldIndex depth index) (word (depth + 1) (depth + 1) lost)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        SourceGraphGrowth.forgettingLoss depth index read value := by
  have original := SourceGraphGrowth.forgetting_realization round depth index read value
  rw [original_loss_formula] at original
  exact original

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
