import H0mework.Versions.X.Fock.HistoryModel.Window

/-! The actual native next produces its refined model value before its inverse-fibre membership is proved. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FamilyModel.Fock

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def nextValue (depth : Nat) : WholeModel (depth + 1) :=
  point (depth + 1) (runtimeAt depth).tick.next.current.visit.current

theorem nextValue_restrict (depth : Nat) :
    forgetLast depth (nextValue depth) = action depth (point depth (runtimeAt depth).current.visit.current) :=
  (forgetLast_point depth _).trans
    ((congrArg (point depth) (runtime_current_next depth)).trans
      ((congrArg (point depth) (runtimePayload depth).nativeWrite.target_eq).trans
        (point_action depth _).symm))

abbrev NextFibre (depth : Nat) :=
  {value : WholeModel (depth + 1) //
    forgetLast depth value = action depth (point depth (runtimeAt depth).current.visit.current)}

def realizedNext (depth : Nat) : NextFibre depth := ⟨nextValue depth, nextValue_restrict depth⟩

theorem next_fibre_iff (depth : Nat) (candidate : WholeModel (depth + 1)) :
    forgetLast depth candidate = action depth (point depth (runtimeAt depth).current.visit.current) ↔
      candidate - nextValue depth ∈ LinearMap.ker (forgetLast depth) := by
  rw [LinearMap.mem_ker, map_sub, nextValue_restrict, sub_eq_zero]

def newestIndex (depth : Nat) : Index (depth + 1) :=
  Fin.last (NativeWindow.bound (runtimeAt (depth + 1)).current.visit.current)

theorem newest_material (depth : Nat) :
    NativeCopy.Fock.material (depth + 1) (newestIndex depth) = (runtimePayload depth).nativeWrite.target :=
  (NativeWindow.last_source (runtimeAt (depth + 1)).current.visit.current (runtimeActive (depth + 1)).down).trans
    (runtime_current_next depth)

theorem newest_readout (depth : Nat) :
    readout (depth + 1) (realizedNext depth).val (newestIndex depth) =
      sourceStateAt (NativeCopy.copy (runtimePayload depth).nativeWrite.target (runtimePayload depth).nativeWrite.target) :=
  (point_read (depth + 1) _ (newestIndex depth)).trans
    (congrArg₂ (fun material state => sourceStateAt (NativeCopy.copy material state))
      (newest_material depth) (runtime_current_next depth))

end
end SourceOwnedObservationHistory.FamilyModel.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
