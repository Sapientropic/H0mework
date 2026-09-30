import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundarySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalBoundary

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (Packet time finitePhases)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def lastCell (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) : Packet depth index :=
  Pi.single (Fin.last index.val) value

theorem extended_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    recordedPrefix runtime index steps (index.val + 1) target =
      SourceCopyTimeModel.extend (inventoryBound runtime) index (finitePhases runtime index steps target) +
        Pi.single (Fin.last (index.val + 1)) (boundary runtime index steps target) := by
  funext phase
  refine Fin.lastCases ?_ (fun earlier => ?_) phase
  · simp only [Pi.add_apply, SourceCopyTimeModel.extend, LinearMap.pi_apply, Fin.lastCases_last,
      LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same]
    rw [prefix_source]
    change observer runtime index steps (time (index.val + 1) target) =
      SourceJointClockGraph.action (observer runtime index steps target) + boundary runtime index steps target
    rw [← SourceCopyProgram.scale_source (inventoryBound runtime) index, boundary]
    abel
  · simp only [Pi.add_apply, SourceCopyTimeModel.extend, LinearMap.pi_apply, Fin.lastCases_castSucc,
      LinearMap.proj_apply, Pi.single_eq_of_ne (Fin.castSucc_ne_last earlier), add_zero]
    rw [prefix_source]
    rfl

theorem drop_last (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    dropFirst (R := ℂ) index.val (Pi.single (Fin.last (index.val + 1)) value) = lastCell depth index value := by
  funext phase
  change (Pi.single (Fin.last (index.val + 1)) value : Fin (index.val + 1 + 1) → SourceJointClockGraph.Carrier) phase.succ =
    (Pi.single (Fin.last index.val) value : Fin (index.val + 1) → SourceJointClockGraph.Carrier) phase
  have same : phase.succ = (Fin.last (index.val + 1) : Fin (index.val + 1 + 1)) ↔ phase = Fin.last index.val := by
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_succ, Nat.add_right_cancel_iff]
  simp only [Pi.single_apply, same]

theorem finite_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    finitePhases runtime index steps (SourceJointClockGraph.action target) =
      SourceCopyTimeModel.next (inventoryBound runtime) index (finitePhases runtime index steps target) +
        lastCell (inventoryBound runtime) index (boundary runtime index steps target) := by
  rw [← actual_next, extended_source, map_add, drop_last]
  rfl

theorem observer_error (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.recover (inventoryBound runtime) index (SourceRecordedEvolution.residual runtime index steps target) =
      SourceCopyGraph.recover (inventoryBound runtime) index target - observer runtime index steps target := by
  rw [SourceRecordedEvolution.residual, SourceCopyCofinal.advanced_action, map_sub, SourceCopyGraph.recover_action]
  rfl

theorem boundary_residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    boundary runtime index steps target =
      SourceJointClockGraph.action (SourceCopyGraph.recover (inventoryBound runtime) index
        (SourceRecordedEvolution.residual runtime index steps target)) -
      SourceCopyGraph.recover (inventoryBound runtime) index (SourceRecordedEvolution.residual runtime index steps
        (time (scale (inventoryBound runtime) index) target)) := by
  rw [observer_error, observer_error, map_sub, SourceCopyTimeModel.recover_cycle, boundary]
  abel

end
end SourceCopyTemporalBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
