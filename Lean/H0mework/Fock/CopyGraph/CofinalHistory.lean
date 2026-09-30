import H0mework.Fock.CopyGraph.CofinalProjection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCofinal

open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph SourceGeneratedActionWords.Fock.Dynamic
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section
attribute [local instance] finiteComplete wholeComplete
  SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

abbrev historyImages (depth : Nat) (index : Index depth) (steps : Nat) := image depth index (depth + steps)

theorem history_images_mono (depth : Nat) (index : Index depth) : Monotone (historyImages depth index) := by
  intro left right ordered
  exact image_mono depth index (Nat.add_le_add_left ordered depth)

theorem history_whole_image (depth : Nat) (index : Index depth) :
    (⨆ steps : Nat, historyImages depth index steps).topologicalClosure = (SourceCopyGraph.action depth index).range := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (iSup_le fun steps => image_in_action _ _ _)
      (action_closed_range depth index)
  · rw [← whole_image depth index 0]
    apply Submodule.topologicalClosure_mono
    apply iSup_le
    intro future
    exact (image_mono depth index (Nat.le_add_left _ _)).trans
      (le_iSup (historyImages depth index) (inventoryBound (roundRuntime (0 + future))))

theorem old_action (depth : Nat) (index : Index depth) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index) = SourceCopyGraph.action depth index := rfl

theorem advanced_action (depth : Nat) (index : Index depth) (steps : Nat) :
    SourceCopyGraph.action (depth + steps) (SourceGraphLoss.advancedIndex depth index steps) = SourceCopyGraph.action depth index := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    change SourceCopyGraph.action ((depth + steps) + 1)
      (FamilyModel.Fock.oldIndex (depth + steps) (SourceGraphLoss.advancedIndex depth index steps)) = _
    rw [old_action, previous]

theorem advanced_image (depth : Nat) (index : Index depth) (steps : Nat) :
    image (depth + steps) (SourceGraphLoss.advancedIndex depth index steps) (depth + steps) = historyImages depth index steps := by
  unfold image
  rw [advanced_action]
  rfl

theorem actual_projection (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    (historyImages (inventoryBound runtime) index steps).starProjection target =
      SourceCopyGraph.action (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
        (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
          (SourceRecordedEvolution.recovery runtime index steps target)) := by
  have actual : (image (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (inventoryBound runtime + steps)).starProjection target =
      SourceCopyGraph.action (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
        (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
          (SourceRecordedEvolution.recovery runtime index steps target)) := by
    rw [finite_projection 0, SourceRecordedEvolution.recovery_original 0, SourceCompleteGraph.recovery_canonical]
    exact (SourceConditionalGraphDecoder.realized_action _ _ _ _ _).symm
  simpa only [advanced_image] using actual

theorem predictions_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => SourceCopyGraph.action (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
        (SourceRecordedEvolution.recovery runtime index steps target))) atTop
      (𝓝 (SourceCopyGraph.action (inventoryBound runtime) index (SourceCopyGraph.recover (inventoryBound runtime) index target))) := by
  let _ : ∀ steps : Nat, (historyImages (inventoryBound runtime) index steps).HasOrthogonalProjection := by
    intro steps
    infer_instance
  let _ : CompleteSpace ((⨆ steps : Nat, historyImages (inventoryBound runtime) index steps).topologicalClosure) :=
    (⨆ steps : Nat, historyImages (inventoryBound runtime) index steps).isClosed_topologicalClosure.isComplete.completeSpace_coe
  have original := Submodule.starProjection_tendsto_closure_iSup (historyImages (inventoryBound runtime) index)
    (history_images_mono (inventoryBound runtime) index) target
  simpa only [history_whole_image, whole_projection, actual_projection] using original

theorem recovery_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceRecordedEvolution.recovery runtime index steps target)) atTop
      (𝓝 (SourceCopyGraph.recover (inventoryBound runtime) index target)) := by
  have original := (SourceCopyGraph.recover (inventoryBound runtime) index).continuous.continuousAt.tendsto.comp
    (predictions_tendsto runtime index target)
  simpa only [Function.comp_def, advanced_action, SourceCopyGraph.recover_action] using original

theorem residual_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => SourceRecordedEvolution.residual runtime index steps target) atTop
      (𝓝 (SourceCopyGraph.residual (inventoryBound runtime) index target)) := by
  have original := (tendsto_const_nhds (x := target)).sub (predictions_tendsto runtime index target)
  exact original

end
end SourceCopyCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
