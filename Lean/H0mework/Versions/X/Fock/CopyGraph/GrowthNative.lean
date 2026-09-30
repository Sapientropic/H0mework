import H0mework.Versions.X.Fock.CopyGraph.GrowthCollision
import H0mework.Versions.X.Fock.CopyGraph.GrowthConditional
import H0mework.Versions.X.Fock.HistoryCopy.InformationProjection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAtomicObservation
open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance nativeGrowthMeasurable : MeasurableSpace ParentCarrier := ⊤

def sourceRead (depth : Nat) (index : Index depth) : Nat → ParentCarrier × ParentCarrier :=
  SourceCopyInventory.read (NativeCopy.Fock.material depth index)

theorem old_read_joint (depth : Nat) (index : Index depth) :
    oldRead depth (sourceRead depth index) = SourceCopyObservation.joint depth depth index :=
  (funext (SourceCopyInventory.joint_source depth depth index)).symm

theorem new_read_joint (depth : Nat) (index : Index depth) :
    newRead depth (sourceRead depth index) =
      SourceCopyObservation.joint (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) := by
  apply funext
  intro actor
  rw [SourceCopyInventory.joint_source, old_material]
  rfl

theorem source_read_written (depth : Nat) (index : Index depth) :
    sourceRead depth index (depth + 1) =
      (sourceStateAt (runtimePayload depth).nativeWrite.target,
        sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material depth index) (runtimePayload depth).nativeWrite.target)) :=
  SourceCopyInventory.written_read (NativeCopy.Fock.material depth index) depth

theorem native_record_read (depth : Nat) (value : Space (historyPMF depth)) (actor : Fin (depth + 1)) :
    IsometricRetainedTransfer.transfer
      (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent depth)
      (Actor.currentTransfer depth depth value)
      (Recorded.whole depth depth (SourcePrimeCalculation.recordedQuery depth actor)) = value actor := by
  have original := SourceGeneratedConditionalInventory.full_record_read (runtimeAt depth) depth
  simp only [record_original] at original
  rw [SourceGeneratedAcquisitionContinuation.inventory_bound, runtimeAt_state] at original
  exact original value actor

theorem native_unit_collision : sourceRead 2 (0 : Index 2) 2 = sourceRead 2 (0 : Index 2) 3 := by
  have snapshot := SourceCopyObservation.original_snapshot_collision
  simp only [SourceCopyObservation.before_source] at snapshot
  have joint : SourceCopyObservation.joint 2 3 (0 : Index 2) (2 : Fin 4) =
      SourceCopyObservation.joint 2 3 (0 : Index 2) (3 : Fin 4) := by
    apply Prod.ext
    · change SourceCopyObservation.before 2 3 (2 : Fin 4) = SourceCopyObservation.before 2 3 (3 : Fin 4)
      simpa only [SourceCopyObservation.before_source] using snapshot
    · change SourceCopyObservation.after 2 3 (0 : Index 2) (2 : Fin 4) =
        SourceCopyObservation.after 2 3 (0 : Index 2) (3 : Fin 4)
      simp only [SourceCopyObservation.after_source, SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
      norm_num only [Fin.val_zero, zero_add, Fin.val_ofNat, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
      exact snapshot
  have identified := (SourceCopyInventory.joint_source 2 3 (0 : Index 2) (2 : Fin 4)).symm.trans
    (joint.trans (SourceCopyInventory.joint_source 2 3 (0 : Index 2) (3 : Fin 4)))
  have left := congrArg (SourceCopyInventory.read (NativeCopy.Fock.material 2 (0 : Index 2)))
    (show (2 : Fin 4).val = 2 from by decide)
  have right := congrArg (SourceCopyInventory.read (NativeCopy.Fock.material 2 (0 : Index 2)))
    (show (3 : Fin 4).val = 3 from by decide)
  exact left.symm.trans (identified.trans right)

abbrev pulse (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier :=
  oldAction depth index (sourceRead depth index)
    (SourceConditionalCorrection.one depth (oldRead depth (sourceRead depth index)))

theorem native_old_recovery (depth : Nat) (index : Index depth) :
    oldResidual depth index (sourceRead depth index) (pulse depth index) = 0 :=
  old_exact depth index (sourceRead depth index) _

theorem native_tagged_recovery (depth : Nat) (index : Index depth) :
    taggedResidual depth index (sourceRead depth index) (pulse depth index) = 0 :=
  tagged_exact depth index (sourceRead depth index) _

theorem native_forgotten_cost :
    (1 : ℝ) / 6 ≤ ‖newResidual 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)) (pulse 2 (0 : Index 2))‖ ^ 2 := by
  have paid := collision_cost 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)) (2 : Fin 3) native_unit_collision
    (SourceConditionalCorrection.one 2 (oldRead 2 (sourceRead 2 (0 : Index 2))))
  have one := SourceConditionalCorrection.one_at 2 (oldRead 2 (sourceRead 2 (0 : Index 2))) (2 : Fin 3)
  rw [pullback_at _ _ _ (2 : Fin 3) (source_positive 2 (2 : Fin 3))] at one
  rw [one, norm_one] at paid
  norm_num only [one_pow, Nat.cast_ofNat] at paid
  exact paid

theorem native_forgetting_positive :
    0 < ‖forgettingLoss 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)) (pulse 2 (0 : Index 2))‖ ^ 2 := by
  have same := congrArg (fun value : SourceJointClockGraph.Carrier => ‖value‖ ^ 2)
    (old_target_loss 2 (0 : Index 2) (sourceRead 2 (0 : Index 2))
      (SourceConditionalCorrection.one 2 (oldRead 2 (sourceRead 2 (0 : Index 2)))))
  with_reducible exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6) (native_forgotten_cost.trans_eq same)

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
