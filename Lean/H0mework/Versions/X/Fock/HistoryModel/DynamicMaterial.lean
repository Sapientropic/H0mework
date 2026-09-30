import H0mework.Versions.X.Fock.HistoryModel.DynamicFibre

/-! The actual new material supplies a fresh source letter while every complete inventory position retains its lineage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem all_material_actual (depth : Nat) (index : FamilyModel.Fock.Index (depth + 1)) :
    NativeCopy.Fock.material (depth + 1) index = ((runtimeAt index.val).current.visit.current : Current) :=
  (window_actor_factorizes (depth + 1) index).1

theorem newest_material_actual (depth : Nat) : NativeCopy.Fock.material (depth + 1) (FamilyModel.Fock.newestIndex depth) =
    ((runtimeAt depth).tick.next.current.visit.current : Current) :=
  (FamilyModel.Fock.newest_material depth).trans (runtime_current_next depth).symm

theorem newest_letter_not_old (depth : Nat) (letter : Fock.Letter depth) :
    Sum.inr (FamilyModel.Fock.newestIndex depth) ≠ oldLetter depth letter := by
  cases letter with
  | inl token => intro same; cases same
  | inr index =>
      intro same
      exact newest_not_old depth index (Sum.inr.inj same)

theorem fresh_letter_execution (depth : Nat) :
    Complete.action (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth)) (Complete.nativeNext depth) =
      Complete.point (depth + 1)
        (NativeCopy.copy ((runtimeAt depth).tick.next.current.visit.current : Current)
          ((runtimeAt depth).tick.next.current.visit.current : Current)) := by
  let state : Current := (runtimeAt depth).tick.next.current.visit.current
  exact (congrArg (Complete.action (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth))) (Complete.next_actual depth)).trans
    ((Complete.action_point (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth)) state).trans
      (congrArg (fun material => Complete.point (depth + 1) (NativeCopy.copy material state)) (newest_material_actual depth)))

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
