import H0mework.Fock.CopyGraph.FibreUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead)
open SourceGraphBirth (innovation)
open SourceConditionalGraphDecoder (fieldDecode)
open scoped Classical
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def normalField (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) : FieldSpace (depth + 1) (depth + 1) :=
  (star (beta depth index read supported) / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • SourceGraphBirth.innovationField depth index read -
    normalize depth (depth + 1) (Nat.le_succ depth) (fieldDecode depth depth index (oldRead depth read) ((arrival depth index read supported).adjoint 1))

theorem normal_field_source (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (normalField depth index read supported)) = normal depth index read supported := by
  rw [normalField, map_sub, map_sub, map_smul, map_smul, SourceGraphBirth.innovation_field_source, SourceGraphGrowth.field_retained_target]
  change (star (beta depth index read supported) / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovation depth index read -
    SourceCopyGraph.action depth index (fieldRead depth depth (SourceConditionalGraphDecoder.realizeObserved depth depth (oldRead depth read)
      (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) ((arrival depth index read supported).adjoint 1)))) = _
  rw [SourceConditionalGraphDecoder.realized_action, dual_source]
  rfl

theorem normal_loss_field (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    SourceGraphGrowth.forgettingField depth index read value =
      (inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normalField depth index read supported := by
  apply (Actor.currentPullback (depth + 1) (depth + 1)).injective
  apply SourceGraphBirth.copy_read_injective (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
  change SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (fieldRead (depth + 1) (depth + 1) (SourceGraphGrowth.forgettingField depth index read value)) =
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1)
        ((inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normalField depth index read supported))
  rw [← SourceGraphGrowth.forgetting_original, map_smul, map_smul, normal_field_source, normal_loss_formula depth index read supported]

theorem supported_field_decoder (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value =
      normalize depth (depth + 1) (Nat.le_succ depth) (fieldDecode depth depth index (oldRead depth read) value) +
        (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • SourceGraphBirth.innovationField depth index read -
        (inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normalField depth index read supported := by
  have original := normal_loss_field depth index read supported value
  unfold SourceGraphGrowth.forgettingField at original
  have solved := eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp original).symm)
  rw [SourceGraphBirth.field_decoder_update] at solved
  exact solved

theorem novel_field_decoder (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (novel : read (depth + 1) ∉ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value =
      normalize depth (depth + 1) (Nat.le_succ depth) (fieldDecode depth depth index (oldRead depth read) value) +
        (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • SourceGraphBirth.innovationField depth index read := by
  have absent : read (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth read) := fun present => novel ((atoms_iff _ _ _).mp present)
  have vanished := SourceGraphLoss.novel_direction_zero depth index read absent
  have original := SourceGraphLoss.whole_field_update depth index read value
  rw [vanished, inner_zero_left, zero_div, zero_smul, sub_zero] at original
  exact original

def fieldRecovery (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    FieldSpace (depth + 1) (depth + 1) :=
  normalize depth (depth + 1) (Nat.le_succ depth) (fieldDecode depth depth index (oldRead depth read) value) +
    (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • SourceGraphBirth.innovationField depth index read -
    if supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support then
      (inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normalField depth index read supported else 0

theorem field_recovery_source (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    fieldRecovery depth index read value =
      fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value := by
  by_cases supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support
  · rw [fieldRecovery, dif_pos supported]
    exact (supported_field_decoder depth index read supported value).symm
  · rw [fieldRecovery, dif_neg supported, sub_zero]
    exact (novel_field_decoder depth index read supported value).symm

def fieldRecoveryMap (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace (depth + 1) (depth + 1) :=
  (normalize depth (depth + 1) (Nat.le_succ depth)).comp (fieldDecode depth depth index (oldRead depth read)) +
    (((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹) •
      InnerProductSpace.rankOne ℂ (SourceGraphBirth.innovationField depth index read) (innovation depth index read) -
    if supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support then
      (((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (normalField depth index read supported) (normal depth index read supported) else 0

theorem field_recovery_map_apply (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    fieldRecoveryMap depth index read value = fieldRecovery depth index read value := by
  by_cases supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support
  · simp only [fieldRecoveryMap, fieldRecovery, dif_pos supported, sub_apply, add_apply, ContinuousLinearMap.comp_apply,
      smul_apply, InnerProductSpace.rankOne_apply, smul_smul, div_eq_mul_inv]
    rw [mul_comm (((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹),
      mul_comm (((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)⁻¹)]
  · simp only [fieldRecoveryMap, fieldRecovery, dif_neg supported, sub_zero, add_apply, ContinuousLinearMap.comp_apply,
      smul_apply, InnerProductSpace.rankOne_apply, smul_smul, div_eq_mul_inv]
    rw [mul_comm (((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹)]

theorem field_recovery_linear (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    fieldRecoveryMap depth index read = fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) := by
  apply ContinuousLinearMap.ext
  intro value
  rw [field_recovery_map_apply, field_recovery_source]

theorem original_update_realization (round depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    let change := (inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normalField depth index read supported
    let copied := SourceCopyGraph.complexAction (depth + 1) (FamilyModel.Fock.oldIndex depth index) (word (depth + 1) (depth + 1) change)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        SourceGraphGrowth.forgettingLoss depth index read value := by
  have original := SourceGraphGrowth.forgetting_realization round depth index read value
  rw [normal_loss_field depth index read supported] at original
  exact original

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
