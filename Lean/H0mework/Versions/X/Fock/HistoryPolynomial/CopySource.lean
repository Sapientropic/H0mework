import H0mework.Versions.X.Fock.HistoryPolynomial.Program
import H0mework.Versions.X.Fock.HistoryModel.Window
import H0mework.Versions.X.Fock.SourceHistory.Bridge

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open ArithmeticGeneration
noncomputable section

abbrev Index := FamilyModel.Fock.Index

def scale (depth : Nat) (index : Index depth) : Nat :=
  (NativeCopy.Fock.material depth index).cardinalShadow

def indexAfter (depth : Nat) (index : Index depth) (state : Nat) : Nat :=
  NativeWindow.bound (NativeCopy.copy (NativeCopy.Fock.material depth index) (finiteVisit state).current)

def action (depth : Nat) (index : Index depth) :
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  Finsupp.lmapDomain ℤ ℤ (indexAfter depth index)

theorem scale_source (depth : Nat) (index : Index depth) : scale depth index = index.val + 1 := by
  have same : NativeCopy.Fock.material depth index = (runtimeAt index.val).current.visit.current :=
    (window_actor_factorizes depth index).1
  exact (congrArg UnitHistory.cardinalShadow same).trans (runtimeAt_scanIndex index.val)

theorem scale_pos (depth : Nat) (index : Index depth) : 0 < scale depth index := by
  rw [scale_source]
  omega

theorem index_source (depth : Nat) (index : Index depth) (state : Nat) :
    indexAfter depth index state = (state + 1) * scale depth index - 1 := by
  have same := congrArg (fun current : Current =>
    NativeWindow.bound (NativeCopy.copy (NativeCopy.Fock.material depth index) current)) (finiteVisit_current state)
  apply same.trans
  change ((UnitHistory.generate (state + 1)).joint (NativeCopy.Fock.material depth index)).cardinalShadow - 1 = _
  rw [UnitHistory.cardinalShadow_joint, UnitHistory.cardinalShadow_generate]
  rfl

theorem index_exact (depth : Nat) (index : Index depth) (state : Nat) :
    indexAfter depth index state + 1 = (state + 1) * scale depth index := by
  rw [index_source]
  exact Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (scale_pos depth index))

theorem index_injective (depth : Nat) (index : Index depth) : Function.Injective (indexAfter depth index) := by
  intro left right same
  have eq := congrArg (fun n => n + 1) same
  rw [index_exact, index_exact] at eq
  exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_right (scale_pos depth index) eq)

theorem actual_copy_state (depth : Nat) (index : Index depth) (state : Nat) :
    (finiteVisit (indexAfter depth index state)).current =
      NativeCopy.copy (NativeCopy.Fock.material depth index) (finiteVisit state).current := by
  have generated : UnitHistory.generate (indexAfter depth index state + 1) =
      (UnitHistory.generate (state + 1)).joint (NativeCopy.Fock.material depth index) := by
    apply UnitHistory.eq_of_cardinalShadow_eq
    rw [UnitHistory.cardinalShadow_generate, UnitHistory.cardinalShadow_joint,
      UnitHistory.cardinalShadow_generate, index_exact]
    rfl
  exact (finiteVisit_current _).trans (generated.trans
    (congrArg (NativeCopy.copy (NativeCopy.Fock.material depth index)) (finiteVisit_current state)).symm)

theorem action_point (depth : Nat) (index : Index depth) (state : Nat) :
    action depth index (SourceOperationNative.statePoint process state) =
      SourceOperationNative.statePoint process (indexAfter depth index state) := by
  simp only [action, SourceOperationNative.statePoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
