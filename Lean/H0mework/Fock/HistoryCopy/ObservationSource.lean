import H0mework.Fock.HistoryPolynomial.CopyConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords SourcePrimeHistoryRecovery
open Fock.OriginalHilbert
open NoIslandNoMagic.CanonicalArithmeticState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev Index := SourceCopyProgram.Index

def copySnapshot (depth : Nat) (index : Index depth) (value : Field nativeStep (rawWords depth)) : ParentCarrier :=
  Fock.Dynamic.Hilbert.present depth (Fock.Complete.action depth (.inr index) ((originalField depth).symm value))

def before (depth bound : Nat) : Fin (bound + 1) → ParentCarrier := inputSnapshot depth ∘ Actor.originalRead depth bound

def after (depth bound : Nat) (index : Index depth) : Fin (bound + 1) → ParentCarrier :=
  copySnapshot depth index ∘ Actor.originalRead depth bound

def joint (depth bound : Nat) (index : Index depth) (actor : Fin (bound + 1)) : ParentCarrier × ParentCarrier :=
  (before depth bound actor, after depth bound index actor)

theorem copy_snapshot_point (depth : Nat) (index : Index depth) (current : Current) :
    copySnapshot depth index (fieldPoint nativeStep (rawWords depth) current) =
      sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material depth index) current) := by
  unfold copySnapshot
  rw [← original_point, LinearEquiv.symm_apply_apply, Fock.Complete.action_point]
  exact Fock.Dynamic.Hilbert.unit_complete_read depth _

theorem before_source (depth bound : Nat) (actor : Fin (bound + 1)) :
    before depth bound actor = secondQuantizedState (rawField actor.val) :=
  input_snapshot_actual depth bound actor

theorem after_source (depth bound : Nat) (index : Index depth) (actor : Fin (bound + 1)) :
    after depth bound index actor = secondQuantizedState (rawField (SourceCopyProgram.indexAfter depth index actor.val)) := by
  have read := (congrArg (copySnapshot depth index) (Actor.originalRead_actual depth bound actor)).trans
    (copy_snapshot_point depth index ((runtimeAt actor.val).current.visit.current : Current))
  have inputCurrent := (runtimeAt_current actor.val).trans (finiteVisit_current actor.val).symm
  have targetCurrent := SourceCopyProgram.actual_copy_state depth index actor.val
  have targetRuntime := (finiteVisit_current (SourceCopyProgram.indexAfter depth index actor.val)).trans
    (runtimeAt_current (SourceCopyProgram.indexAfter depth index actor.val)).symm
  have same := (congrArg (NativeCopy.copy (NativeCopy.Fock.material depth index)) inputCurrent).trans
    (targetCurrent.symm.trans targetRuntime)
  exact read.trans (congrArg sourceStateAt same)

theorem before_theta (depth bound : Nat) (actor : Fin (bound + 1)) :
    thetaProjection (before depth bound actor) = rawField actor.val := by
  rw [before_source]
  simp only [secondQuantizedState, map_add, thetaProjection_diagonalInclusion]
  change rawField actor.val + 0 = rawField actor.val
  exact add_zero _

theorem after_theta (depth bound : Nat) (index : Index depth) (actor : Fin (bound + 1)) :
    thetaProjection (after depth bound index actor) = rawField (SourceCopyProgram.indexAfter depth index actor.val) := by
  rw [after_source]
  simp only [secondQuantizedState, map_add, thetaProjection_diagonalInclusion]
  change rawField (SourceCopyProgram.indexAfter depth index actor.val) + 0 = _
  exact add_zero _

theorem joint_before (depth bound : Nat) (index : Index depth) :
    Prod.fst ∘ joint depth bound index = before depth bound := rfl

theorem joint_after (depth bound : Nat) (index : Index depth) :
    Prod.snd ∘ joint depth bound index = after depth bound index := rfl

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
