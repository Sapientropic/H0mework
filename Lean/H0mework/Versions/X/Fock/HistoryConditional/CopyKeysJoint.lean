import H0mework.Versions.X.Fock.HistoryConditional.CopyKeysSupport
import H0mework.Versions.X.Fock.HistoryConditional.CopyBirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeKeys

open SourceOwnedObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open SourcePrimeHistoryRecovery
noncomputable section

private theorem parent_fibre (left right : Nat) :
    secondQuantizedState (rawField left) = secondQuantizedState (rawField right) ↔ rawField left = rawField right := by
  constructor
  · intro same
    have projected := congrArg thetaProjection same
    simp only [secondQuantizedState, map_add, thetaProjection_diagonalInclusion] at projected
    change rawField left + 0 = rawField right + 0 at projected
    exact add_right_cancel projected
  · exact congrArg secondQuantizedState

theorem copy_index (depth : Nat) (index : SourceCopyObservation.Index depth) (state : Nat) :
    SourceCopyProgram.indexAfter depth index state = (state + 1) * (index.val + 1) - 1 := by
  rw [SourceCopyProgram.index_source, SourceCopyProgram.scale_source]

theorem joint_read (depth : Nat) (index : SourceCopyObservation.Index depth) (state : Nat) :
    SourceCopyInventory.read (NativeCopy.Fock.material depth index) state =
      (secondQuantizedState (rawField state), secondQuantizedState (rawField ((state + 1) * (index.val + 1) - 1))) := by
  have original := SourceCopyInventory.joint_source depth state index (Fin.last state)
  have before := SourceCopyObservation.before_source depth state (Fin.last state)
  have after := SourceCopyObservation.after_source depth state index (Fin.last state)
  rw [copy_index] at after
  exact original.symm.trans (Prod.ext before after)

theorem joint_fibre (depth : Nat) (index : SourceCopyObservation.Index depth) (left right : Nat) :
    jointKey index.val left = jointKey index.val right ↔
      SourceCopyInventory.read (NativeCopy.Fock.material depth index) left =
        SourceCopyInventory.read (NativeCopy.Fock.material depth index) right := by
  rw [joint_read, joint_read]
  simp only [jointKey, Prod.mk.injEq, parent_fibre, ← key_fibre]

theorem original_fibre (depth bound : Nat) (index : SourceCopyObservation.Index depth) (left right : Fin (bound + 1)) :
    jointKey index.val left.val = jointKey index.val right.val ↔
      SourceCopyObservation.joint depth bound index left = SourceCopyObservation.joint depth bound index right := by
  rw [SourceCopyInventory.joint_source, SourceCopyInventory.joint_source]
  exact joint_fibre depth index left.val right.val

end
end SourceCopyNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
