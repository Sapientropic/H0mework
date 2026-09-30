import H0mework.Fock.HistoryConditional.NativeKeys.Material
import H0mework.Fock.HistoryConditional.RationalStreamMaterial
import H0mework.Fock.HistoryConditional.WordStreamMaterial
import H0mework.Fock.HistoryConditional.FiniteStreamMaterial
import H0mework.Fock.HistoryConditional.StreamMaterial
import H0mework.Fock.HistoryConditional.StabilityMaterial
import H0mework.Fock.HistoryConditional.PosteriorMaterial
import H0mework.Fock.HistoryConditional.ModelUpdateMaterial
import H0mework.Fock.HistoryConditional.InnovationMaterial
import H0mework.Fock.HistoryConditional.InformationMaterial
import H0mework.Fock.HistoryConditional.GCostMaterial
import H0mework.Fock.HistoryConditional.ActualImageMaterial
import H0mework.Fock.HistoryConditional.InventoryMaterial
import H0mework.Fock.HistoryConditional.VectorMaterial
import H0mework.Fock.HistoryConditional.ModelMaterial
import H0mework.Fock.CopyGraph.Phase.Material
import H0mework.Fock.CopyGraph.SharedHistory.Material
import H0mework.Fock.CopyGraph.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index)
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceCopyTemporalBoundary (observer)
open SourceCopyFutureCoordinates (realize modelEquiv residual)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageBudget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (stage : Nat) → SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage) → Prop
  | 0, material =>
      ‖realize runtime index 0 (modelEquiv runtime index 0 (cache runtime index 0))‖ ^ 2 +
        ‖residual runtime index 0 (sourceValue material.next)‖ ^ 2 = ‖sourceValue material.next‖ ^ 2
  | stage + 1, material =>
      ‖advanceGain runtime index stage (cache runtime index stage)
        (SourceCopyFutureUpdate.samples runtime index stage (sourceValue (runtime.advance (stage + 1))))‖ ^ 2 +
        ‖residual runtime index (stage + 1) (sourceValue material.next)‖ ^ 2 =
          ‖residual runtime index stage (sourceValue (runtime.advance (stage + 1)))‖ ^ 2

def StageLaw (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) : Prop :=
  ∀ index : Index (inventoryBound runtime),
    cache runtime index stage = projection SourceJointClockGraph.action.toLinearMap (observer runtime index (stage + 1))
      (sourceValue material.next) ∧ StageBudget runtime index stage material

theorem stage_law (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) : StageLaw runtime stage material := by
  intro index
  refine ⟨cache_at_material runtime index stage material, ?_⟩
  cases stage with
  | zero =>
      dsimp only [StageBudget]
      rw [cache_at_material runtime index 0 material, SourceCopyFutureCoordinates.model_equiv_source]
      exact SourceCopyFutureCoordinates.energy runtime index 0 (sourceValue material.next)
  | succ stage => exact cache_gain_budget runtime index stage material

def LiveStageLaw (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) : Prop :=
  SourceCopyLiveModelFamily.MaterialLaw (runtime.advance stage) material ∧
    (∀ index : Index (inventoryBound (runtime.advance stage)),
      StageBudget (runtimeAt index.val) (SourceCopyLiveModelFamily.birthIndex index.val)
        (SourceCopyLiveModelFamily.age (runtime.advance stage) index)
        (SourceGeneratedRuntimeMaterialStageAt.generate
          ((runtimeAt index.val).advance (SourceCopyLiveModelFamily.age (runtime.advance stage) index)))) ∧
    SourceCopySharedHistory.StageLaw runtime stage material ∧
    SourceCopyPhaseRecovery.StageLaw (runtime.advance stage) material ∧
    SourceConditionalModel.StageLaw (runtime.advance stage) material ∧
    SourceConditionalVector.StageLaw (runtime.advance stage) material ∧
    SourceConditionalInventory.StageLaw (runtime.advance stage) material ∧
    SourceActualImageStep.StageLaw (runtime.advance stage) material ∧
    SourceGInformationCost.StageLaw (runtime.advance stage) material ∧
    SourceInformationReadback.StageLaw (runtime.advance stage) material ∧
    SourceConditionalInnovation.StageLaw (runtime.advance stage) material ∧
    SourceConditionalModelUpdate.StageLaw (runtime.advance stage) material ∧
    SourcePosteriorReadback.StageLaw (runtime.advance stage) material ∧
    SourcePosteriorStability.StageLaw (runtime.advance stage) material ∧
    SourceConditionalStream.StageLaw (runtime.advance stage) material ∧
    SourceConditionalFiniteStream.StageLaw (runtime.advance stage) material ∧
    SourceConditionalWordStream.StageLaw (runtime.advance stage) material ∧
    SourceConditionalRationalStream.StageLaw (runtime.advance stage) material ∧
    SourceConditionalNativeKeys.StageLaw (runtime.advance stage) material

theorem live_stage_law (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) : LiveStageLaw runtime stage material :=
  ⟨SourceCopyLiveModelFamily.material_law (runtime.advance stage) material,
    (fun index => ((stage_law (runtimeAt index.val) (SourceCopyLiveModelFamily.age (runtime.advance stage) index)
      (SourceGeneratedRuntimeMaterialStageAt.generate
        ((runtimeAt index.val).advance (SourceCopyLiveModelFamily.age (runtime.advance stage) index))))
          (SourceCopyLiveModelFamily.birthIndex index.val)).2),
    SourceCopySharedHistory.stage_law runtime stage material,
    SourceCopyPhaseRecovery.stage_law (runtime.advance stage) material,
    SourceConditionalModel.stage_law (runtime.advance stage) material,
    SourceConditionalVector.stage_law (runtime.advance stage) material,
    SourceConditionalInventory.stage_law (runtime.advance stage) material,
    SourceActualImageStep.stage_law (runtime.advance stage) material,
    SourceGInformationCost.stage_law (runtime.advance stage) material,
    SourceInformationReadback.stage_law (runtime.advance stage) material,
    SourceConditionalInnovation.stage_law (runtime.advance stage) material,
    SourceConditionalModelUpdate.stage_law (runtime.advance stage) material,
    SourcePosteriorReadback.stage_law (runtime.advance stage) material,
    SourcePosteriorStability.stage_law (runtime.advance stage) material,
    SourceConditionalStream.stage_law (runtime.advance stage) material,
    SourceConditionalFiniteStream.stage_law (runtime.advance stage) material,
    SourceConditionalWordStream.stage_law (runtime.advance stage) material,
    SourceConditionalRationalStream.stage_law (runtime.advance stage) material,
    SourceConditionalNativeKeys.stage_law (runtime.advance stage) material⟩

-- Only the source-fixed local laws are strengthened; the root, active face,
-- exact material history and stage count are the original ones.
private def sourceFrontier (runtime : LivingRuntimeState process) :
    SourceNativeRuntimeCalculationFrontierAt runtimeFacade runtime .particleWave :=
  .ofActive (frontier runtime).active (frontier runtime).classifier_eq (frontier runtime).stageCount
    (fun stage payload material => (frontier runtime).LocalOperationAt stage payload material ∧
      StageLaw runtime stage.val material ∧ LiveStageLaw runtime stage.val material)

private theorem realization (runtime : LivingRuntimeState process) :
    SourceNativeRuntimeCalculationRealizationAt (sourceFrontier runtime) where
  operationAt stage := by
    change Fin ((frontier runtime).stageCount + 1) at stage
    change (frontier runtime).LocalOperationAt stage (frontier runtime).sourcePayload ((frontier runtime).history.stageAt stage) ∧
      StageLaw runtime stage.val ((frontier runtime).history.stageAt stage) ∧
      LiveStageLaw runtime stage.val ((frontier runtime).history.stageAt stage)
    exact ⟨(SourceGeneratedAcquisitionContinuation.realization runtime).operationAt stage,
      stage_law runtime stage.val ((sourceFrontier runtime).history.stageAt stage),
      live_stage_law runtime stage.val ((sourceFrontier runtime).history.stageAt stage)⟩

def calculationNormal (runtime : LivingRuntimeState process) :
    SourceGeneratedRuntimeCalculationNormalFormAt (realization runtime) := .generate (realization runtime)

theorem calculated_stage (runtime : LivingRuntimeState process)
    (stage : Fin ((frontier runtime).stageCount + 1)) :
    (frontier runtime).LocalOperationAt stage (frontier runtime).sourcePayload ((frontier runtime).history.stageAt stage) ∧
      StageLaw runtime stage.val ((frontier runtime).history.stageAt stage) ∧
      LiveStageLaw runtime stage.val ((frontier runtime).history.stageAt stage) :=
  (realization runtime).operationAt stage

theorem normal_target_original (runtime : LivingRuntimeState process) :
    (calculationNormal runtime).targetRuntime = (normal runtime).targetRuntime := rfl

theorem calculated_cache_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (stage : Fin ((frontier runtime).stageCount + 1)) :
    cache runtime index stage.val = projection SourceJointClockGraph.action.toLinearMap (observer runtime index (stage.val + 1))
      (sourceValue ((frontier runtime).history.stageAt stage).next) :=
  ((calculated_stage runtime stage).2.1 index).1

theorem normal_cache_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    cache runtime index (frontier runtime).stageCount =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index ((frontier runtime).stageCount + 1))
        (sourceValue (calculationNormal runtime).targetRuntime) :=
  calculated_cache_source runtime index (Fin.last (frontier runtime).stageCount)

theorem next_cache_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    cache runtime index ((frontier runtime).stageCount + 1) =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index ((frontier runtime).stageCount + 2))
        (sourceValue (calculationNormal runtime).targetRuntime.tick.next) := by
  let material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance ((frontier runtime).stageCount + 1)) :=
    .generate (calculationNormal runtime).targetRuntime
  exact ((stage_law runtime ((frontier runtime).stageCount + 1) material) index).1

theorem normal_live_source (runtime : LivingRuntimeState process) :
    SourceCopyLiveModelFamily.CurrentLaw (calculationNormal runtime).targetRuntime :=
  (calculated_stage runtime (Fin.last (frontier runtime).stageCount)).2.2.1.2.1

theorem next_live_source (runtime : LivingRuntimeState process) :
    SourceCopyLiveModelFamily.CurrentLaw (calculationNormal runtime).targetRuntime.tick.next :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).1.2.1

theorem calculated_history (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceCopySharedHistory.StageLaw runtime stage.val ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.1

theorem normal_history_source (runtime : LivingRuntimeState process) :
    SourceCopySharedHistory.history runtime ((frontier runtime).stageCount + 1) =
      SourceCopyCurrentCoordinates.shared (calculationNormal runtime).targetRuntime :=
  (calculated_history runtime (Fin.last (frontier runtime).stageCount)).1

theorem normal_history_family (runtime : LivingRuntimeState process) :
    SourceCopyCurrentCoordinates.expand (calculationNormal runtime).targetRuntime
      (SourceCopySharedHistory.history runtime ((frontier runtime).stageCount + 1)) =
        SourceCopyLiveModelFamily.family (calculationNormal runtime).targetRuntime :=
  (calculated_history runtime (Fin.last (frontier runtime).stageCount)).2.1

theorem normal_history_budget (runtime : LivingRuntimeState process) :
    type_of% (SourceCopySharedHistory.history_budget runtime ((frontier runtime).stageCount + 1)) := by
  have paid := calculated_history runtime (Fin.last (frontier runtime).stageCount)
  dsimp only [SourceCopySharedHistory.StageLaw, Fin.last] at paid
  with_reducible exact paid.2.2.2.1

theorem next_history_source (runtime : LivingRuntimeState process) :
    SourceCopySharedHistory.history runtime ((frontier runtime).stageCount + 2) =
      SourceCopyCurrentCoordinates.shared (calculationNormal runtime).targetRuntime.tick.next :=
  (SourceCopySharedHistory.stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).1

theorem calculated_phase (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceCopyPhaseRecovery.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.1

theorem normal_phase (runtime : LivingRuntimeState process) :
    SourceCopyPhaseRecovery.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_phase runtime (Fin.last (frontier runtime).stageCount)

theorem normal_phase_budget (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    type_of% (SourceCopyPhaseRecovery.phase_budget (runtime.advance (frontier runtime).stageCount) target) := by
  have paid := normal_phase runtime
  dsimp only [SourceCopyPhaseRecovery.StageLaw] at paid
  with_reducible exact (paid.1 target).1

theorem next_phase (runtime : LivingRuntimeState process) :
    SourceCopyPhaseRecovery.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.1

theorem normal_native_history (runtime : LivingRuntimeState process) :
    type_of% (SourceCopySharedHistory.history_native_step runtime (frontier runtime).stageCount) := by
  have paid := calculated_history runtime (Fin.last (frontier runtime).stageCount)
  dsimp only [SourceCopySharedHistory.StageLaw, Fin.last] at paid
  with_reducible exact paid.2.2.2.2.1

theorem normal_native_model (runtime : LivingRuntimeState process) :
    type_of% (SourceCopySharedHistory.model_history_native_step runtime (frontier runtime).stageCount) := by
  have paid := calculated_history runtime (Fin.last (frontier runtime).stageCount)
  dsimp only [SourceCopySharedHistory.StageLaw, Fin.last] at paid
  with_reducible exact paid.2.2.2.2.2.1

theorem normal_native_energy (runtime : LivingRuntimeState process) :
    type_of% (SourceCopySharedHistory.history_native_energy runtime (frontier runtime).stageCount) := by
  have paid := calculated_history runtime (Fin.last (frontier runtime).stageCount)
  dsimp only [SourceCopySharedHistory.StageLaw, Fin.last] at paid
  with_reducible exact paid.2.2.2.2.2.2.1

theorem next_native_history (runtime : LivingRuntimeState process) :
    type_of% (SourceCopySharedHistory.history_native_step runtime ((frontier runtime).stageCount + 1)) := by
  have paid := (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.1
  dsimp only [SourceCopySharedHistory.StageLaw] at paid
  with_reducible exact paid.2.2.2.2.1

theorem calculated_information (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalModel.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.1

theorem normal_information (runtime : LivingRuntimeState process) :
    SourceConditionalModel.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_information runtime (Fin.last (frontier runtime).stageCount)

theorem normal_information_variance (runtime : LivingRuntimeState process) (depth : Nat)
    (decode : SourceConditionalModel.NextModel (runtime.advance (frontier runtime).stageCount) → ℂ) :
    type_of% (SourceConditionalModel.variance_original_account (runtime.advance (frontier runtime).stageCount) depth decode) := by
  have paid := normal_information runtime
  dsimp only [SourceConditionalModel.StageLaw] at paid
  with_reducible exact (paid.2.2.2.1 depth decode).1

theorem next_information (runtime : LivingRuntimeState process) :
    SourceConditionalModel.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.1

theorem calculated_vector (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalVector.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.1

theorem normal_vector (runtime : LivingRuntimeState process) :
    SourceConditionalVector.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_vector runtime (Fin.last (frontier runtime).stageCount)

theorem normal_vector_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalVector.dynamic_attains (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_vector runtime
  dsimp only [SourceConditionalVector.StageLaw] at paid
  with_reducible exact (paid.2.2.1 depth).2.2.1

theorem next_vector (runtime : LivingRuntimeState process) :
    SourceConditionalVector.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.1

theorem calculated_inventory (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalInventory.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.1

theorem normal_inventory (runtime : LivingRuntimeState process) :
    SourceConditionalInventory.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_inventory runtime (Fin.last (frontier runtime).stageCount)

theorem normal_inventory_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalInventory.current_total_minimum (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_inventory runtime
  dsimp only [SourceConditionalInventory.StageLaw] at paid
  with_reducible exact (paid.2.2.2.2.1 depth).2.2.2.2

theorem next_inventory (runtime : LivingRuntimeState process) :
    SourceConditionalInventory.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.1

theorem calculated_image (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceActualImageStep.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.1

theorem normal_image (runtime : LivingRuntimeState process) :
    SourceActualImageStep.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_image runtime (Fin.last (frontier runtime).stageCount)

theorem normal_image_recovery (runtime : LivingRuntimeState process) :
    type_of% (SourceActualImageStep.recover_first (runtime.advance (frontier runtime).stageCount)) := by
  have paid := normal_image runtime
  dsimp only [SourceActualImageStep.StageLaw] at paid
  with_reducible exact paid.2.2.2.2.1

theorem next_image (runtime : LivingRuntimeState process) :
    SourceActualImageStep.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.1

theorem calculated_g_information (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceGInformationCost.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.1

theorem normal_g_information (runtime : LivingRuntimeState process) :
    SourceGInformationCost.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_g_information runtime (Fin.last (frontier runtime).stageCount)

theorem normal_g_information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceGInformationCost.current_full_variance (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_g_information runtime
  dsimp only [SourceGInformationCost.StageLaw] at paid
  with_reducible exact (paid.2.1 depth).2.1

theorem next_g_information (runtime : LivingRuntimeState process) :
    SourceGInformationCost.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.1

theorem calculated_information_readback (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceInformationReadback.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_information_readback (runtime : LivingRuntimeState process) :
    SourceInformationReadback.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_information_readback runtime (Fin.last (frontier runtime).stageCount)

theorem normal_information_budget (runtime : LivingRuntimeState process) (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    type_of% (SourceInformationReadback.dynamic_budget_inventory (runtime.advance (frontier runtime).stageCount) depth decoder) := by
  have paid := normal_information_readback runtime
  dsimp only [SourceInformationReadback.StageLaw] at paid
  with_reducible exact ((paid.1 depth).2.2.2.2.2 decoder).2.2

theorem next_information_readback (runtime : LivingRuntimeState process) :
    SourceInformationReadback.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.1

theorem calculated_innovation (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalInnovation.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_innovation (runtime : LivingRuntimeState process) :
    SourceConditionalInnovation.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_innovation runtime (Fin.last (frontier runtime).stageCount)

theorem normal_innovation_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalInnovation.update_error_current (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_innovation runtime
  dsimp only [SourceConditionalInnovation.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.2.1

theorem next_innovation (runtime : LivingRuntimeState process) :
    SourceConditionalInnovation.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.1

theorem calculated_model_update (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalModelUpdate.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_model_update (runtime : LivingRuntimeState process) :
    SourceConditionalModelUpdate.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_model_update runtime (Fin.last (frontier runtime).stageCount)

theorem normal_model_update_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalModelUpdate.update_error (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_model_update runtime
  dsimp only [SourceConditionalModelUpdate.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.1

theorem next_model_update (runtime : LivingRuntimeState process) :
    SourceConditionalModelUpdate.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_posterior_readback (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourcePosteriorReadback.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_posterior_readback (runtime : LivingRuntimeState process) :
    SourcePosteriorReadback.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_posterior_readback runtime (Fin.last (frontier runtime).stageCount)

theorem normal_posterior_information (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourcePosteriorReadback.recovered_information_cost (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_posterior_readback runtime
  dsimp only [SourcePosteriorReadback.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.1

theorem next_posterior_readback (runtime : LivingRuntimeState process) :
    SourcePosteriorReadback.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_posterior_stability (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourcePosteriorStability.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_posterior_stability (runtime : LivingRuntimeState process) :
    SourcePosteriorStability.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_posterior_stability runtime (Fin.last (frontier runtime).stageCount)

theorem normal_posterior_error (runtime : LivingRuntimeState process) (depth : Nat)
    (models : Field parity → SourceConditionalModel.NextModel (runtime.advance (frontier runtime).stageCount)) :
    type_of% (SourcePosteriorStability.profile_error_budget (runtime.advance (frontier runtime).stageCount) depth models) := by
  have paid := normal_posterior_stability runtime
  dsimp only [SourcePosteriorStability.StageLaw] at paid
  with_reducible exact paid.1 depth models

theorem next_posterior_stability (runtime : LivingRuntimeState process) :
    SourcePosteriorStability.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_conditional_stream (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalStream.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_conditional_stream (runtime : LivingRuntimeState process) :
    SourceConditionalStream.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_conditional_stream runtime (Fin.last (frontier runtime).stageCount)

theorem normal_conditional_stream_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalStream.generated_error_next (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_conditional_stream runtime
  dsimp only [SourceConditionalStream.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.2.2.2.1

theorem next_conditional_stream (runtime : LivingRuntimeState process) :
    SourceConditionalStream.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_finite_stream (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalFiniteStream.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_finite_stream (runtime : LivingRuntimeState process) :
    SourceConditionalFiniteStream.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_finite_stream runtime (Fin.last (frontier runtime).stageCount)

theorem normal_finite_stream_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalFiniteStream.error_next (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_finite_stream runtime
  dsimp only [SourceConditionalFiniteStream.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.2.2.2.2.1

theorem next_finite_stream (runtime : LivingRuntimeState process) :
    SourceConditionalFiniteStream.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_word_stream (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalWordStream.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_word_stream (runtime : LivingRuntimeState process) :
    SourceConditionalWordStream.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_word_stream runtime (Fin.last (frontier runtime).stageCount)

theorem normal_word_stream_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalWordStream.error_next (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_word_stream runtime
  dsimp only [SourceConditionalWordStream.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.2.1

theorem next_word_stream (runtime : LivingRuntimeState process) :
    SourceConditionalWordStream.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_rational_stream (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalRationalStream.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normal_rational_stream (runtime : LivingRuntimeState process) :
    SourceConditionalRationalStream.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_rational_stream runtime (Fin.last (frontier runtime).stageCount)

theorem normal_rational_stream_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalRationalStream.error_next (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_rational_stream runtime
  dsimp only [SourceConditionalRationalStream.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.2.2.1

theorem next_rational_stream (runtime : LivingRuntimeState process) :
    SourceConditionalRationalStream.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calculated_native_keys (runtime : LivingRuntimeState process) (stage : Fin ((frontier runtime).stageCount + 1)) :
    SourceConditionalNativeKeys.StageLaw (runtime.advance stage.val) ((frontier runtime).history.stageAt stage) :=
  (calculated_stage runtime stage).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem normal_native_keys (runtime : LivingRuntimeState process) :
    SourceConditionalNativeKeys.StageLaw (runtime.advance (frontier runtime).stageCount)
      ((frontier runtime).history.stageAt (Fin.last (frontier runtime).stageCount)) :=
  calculated_native_keys runtime (Fin.last (frontier runtime).stageCount)

theorem normal_native_keys_error (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceConditionalNativeKeys.error_next (runtime.advance (frontier runtime).stageCount) depth) := by
  have paid := normal_native_keys runtime
  dsimp only [SourceConditionalNativeKeys.StageLaw] at paid
  with_reducible exact (paid.1 depth).2.2.1

theorem next_native_keys (runtime : LivingRuntimeState process) :
    SourceConditionalNativeKeys.StageLaw (calculationNormal runtime).targetRuntime
      (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime) :=
  (live_stage_law runtime ((frontier runtime).stageCount + 1)
    (SourceGeneratedRuntimeMaterialStageAt.generate (calculationNormal runtime).targetRuntime)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem normal_native_keys_full_error (runtime : LivingRuntimeState process) :
    type_of% (SourceConditionalNativeObservers.error_zero (runtime.advance (frontier runtime).stageCount)) := by
  have paid := normal_native_keys runtime
  dsimp only [SourceConditionalNativeKeys.StageLaw] at paid
  with_reducible exact paid.2.2.2.2.2.1

theorem normal_native_keys_full_update (runtime : LivingRuntimeState process)
    (actor : SourceConditionalModel.Actors (runtime.advance (frontier runtime).stageCount).tick.next) :
    type_of% (SourceConditionalNativeObservers.next_recovers (runtime.advance (frontier runtime).stageCount) actor) := by
  have paid := normal_native_keys runtime
  dsimp only [SourceConditionalNativeKeys.StageLaw] at paid
  with_reducible exact paid.2.2.2.2.2.2.2 actor

theorem calculation_consumed (runtime : LivingRuntimeState process) :
    type_of% (calculationNormal runtime).target_factorizes ∧
      (calculationNormal runtime).targetRuntime = (normal runtime).targetRuntime ∧
      (∀ stage : Fin ((frontier runtime).stageCount + 1),
        (frontier runtime).LocalOperationAt stage (frontier runtime).sourcePayload ((frontier runtime).history.stageAt stage) ∧
          StageLaw runtime stage.val ((frontier runtime).history.stageAt stage) ∧
          LiveStageLaw runtime stage.val ((frontier runtime).history.stageAt stage)) ∧
      (∀ index : Index (inventoryBound runtime), type_of% (normal_cache_source runtime index) ∧ type_of% (next_cache_source runtime index)) ∧
      SourceCopyLiveModelFamily.CurrentLaw (calculationNormal runtime).targetRuntime ∧
      SourceCopyLiveModelFamily.CurrentLaw (calculationNormal runtime).targetRuntime.tick.next ∧
      type_of% (normal_history_source runtime) ∧ type_of% (normal_history_family runtime) ∧
      type_of% (normal_history_budget runtime) ∧ type_of% (next_history_source runtime) ∧
      type_of% (normal_phase runtime) ∧ type_of% (next_phase runtime) ∧
      type_of% (normal_native_history runtime) ∧ type_of% (normal_native_model runtime) ∧
      type_of% (normal_native_energy runtime) ∧ type_of% (next_native_history runtime) ∧
      type_of% (normal_information runtime) ∧ type_of% (next_information runtime) ∧
      type_of% (normal_vector runtime) ∧ type_of% (next_vector runtime) ∧
      type_of% (normal_inventory runtime) ∧ type_of% (next_inventory runtime) ∧
      type_of% (normal_image runtime) ∧ type_of% (next_image runtime) ∧
      type_of% (normal_g_information runtime) ∧ type_of% (next_g_information runtime) ∧
      type_of% (normal_information_readback runtime) ∧ type_of% (next_information_readback runtime) ∧
      type_of% (normal_innovation runtime) ∧ type_of% (next_innovation runtime) ∧
      type_of% (normal_model_update runtime) ∧ type_of% (next_model_update runtime) ∧
      type_of% (normal_posterior_readback runtime) ∧ type_of% (next_posterior_readback runtime) ∧
      type_of% (normal_posterior_stability runtime) ∧ type_of% (next_posterior_stability runtime) ∧
      type_of% (normal_conditional_stream runtime) ∧ type_of% (next_conditional_stream runtime) ∧
      type_of% (normal_finite_stream runtime) ∧ type_of% (next_finite_stream runtime) ∧
      type_of% (normal_word_stream runtime) ∧ type_of% (next_word_stream runtime) ∧
      type_of% (normal_rational_stream runtime) ∧ type_of% (next_rational_stream runtime) ∧
      type_of% (normal_native_keys runtime) ∧ type_of% (next_native_keys runtime) := by
  with_reducible exact ⟨(calculationNormal runtime).target_factorizes, normal_target_original runtime,
    calculated_stage runtime, (fun index => ⟨normal_cache_source runtime index, next_cache_source runtime index⟩),
    normal_live_source runtime, next_live_source runtime, normal_history_source runtime, normal_history_family runtime,
    normal_history_budget runtime, next_history_source runtime, normal_phase runtime, next_phase runtime,
    normal_native_history runtime, normal_native_model runtime, normal_native_energy runtime, next_native_history runtime,
    normal_information runtime, next_information runtime, normal_vector runtime, next_vector runtime,
    normal_inventory runtime, next_inventory runtime, normal_image runtime, next_image runtime,
    normal_g_information runtime, next_g_information runtime, normal_information_readback runtime, next_information_readback runtime,
    normal_innovation runtime, next_innovation runtime, normal_model_update runtime, next_model_update runtime,
    normal_posterior_readback runtime, next_posterior_readback runtime, normal_posterior_stability runtime, next_posterior_stability runtime,
    normal_conditional_stream runtime, next_conditional_stream runtime, normal_finite_stream runtime, next_finite_stream runtime,
    normal_word_stream runtime, next_word_stream runtime, normal_rational_stream runtime, next_rational_stream runtime,
    normal_native_keys runtime, next_native_keys runtime⟩

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
