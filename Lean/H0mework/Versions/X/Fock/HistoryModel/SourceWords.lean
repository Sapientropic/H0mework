import H0mework.Realization.ObservationActions.WordsModel
import H0mework.Versions.X.Fock.HistoryModel.Installed

/-! The original entire past material inventory supplies the permitted copy letters beside its native step. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

abbrev Letter (depth : Nat) := Unit ⊕ FamilyModel.Fock.Index depth

def step (depth : Nat) : Letter depth → Current → Current
  | .inl _ => nativeStep
  | .inr index => NativeCopy.copy (NativeCopy.Fock.material depth index)

def actions (depth : Nat) (letter : Letter depth) : Carrier Current →ₗ[ℤ] Carrier Current :=
  sourceAction (step depth letter)

def observer (depth : Nat) : Carrier Current →ₗ[ℤ] (FamilyModel.Fock.Index depth → ParentCarrier) :=
  observation (FamilyModel.familyRead (FamilyModel.Fock.reader depth))

abbrev WholeModel (depth : Nat) := Model (actions depth) (observer depth) (.inl ())

def point (depth : Nat) (state : Current) : WholeModel depth :=
  projection (actions depth) (observer depth) (.inl ()) (sourcePoint state)

abbrev letterAction (depth : Nat) := advance (actions depth) (observer depth) (.inl ())

def restrict (depth : Nat) : WholeModel depth →ₗ[ℤ] FamilyModel.Fock.WholeModel depth :=
  originalRestriction (actions depth) (observer depth) (.inl ())

theorem restrict_point (depth : Nat) (state : Current) :
    restrict depth (point depth state) = FamilyModel.Fock.point depth state :=
  originalRestriction_source (actions depth) (observer depth) (.inl ()) (sourcePoint state)

theorem action_point (depth : Nat) (letter : Letter depth) (state : Current) :
    letterAction depth letter (point depth state) = point depth (step depth letter state) := by
  change advance (actions depth) (observer depth) (.inl ()) letter
    (projection (actions depth) (observer depth) (.inl ()) (sourcePoint state)) = _
  rw [advance_source]
  exact congrArg (projection (actions depth) (observer depth) (.inl ()))
    (sourceAction_point (step depth letter) state)

theorem native_restrict (depth : Nat) (value : WholeModel depth) :
    restrict depth (letterAction depth (.inl ()) value) = FamilyModel.Fock.action depth (restrict depth value) :=
  originalRestriction_primary (actions depth) (observer depth) (.inl ()) value

def actualWord (depth : Nat) (word : List (Letter depth)) (state : Current) : Current :=
  word.foldl (fun current letter => step depth letter current) state

theorem word_point (depth : Nat) (word : List (Letter depth)) (state : Current) :
    run (letterAction depth) word (point depth state) = point depth (actualWord depth word state) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter rest previous =>
      change run (letterAction depth) rest (letterAction depth letter (point depth state)) = _
      rw [action_point, previous]
      rfl

theorem read_word (depth : Nat) (word : List (Letter depth)) (state : Current)
    (index : FamilyModel.Fock.Index depth) :
    FamilyModel.Fock.readout depth (restrict depth (run (letterAction depth) word (point depth state))) index =
      sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material depth index) (actualWord depth word state)) := by
  rw [word_point, restrict_point]
  exact FamilyModel.Fock.point_read depth (actualWord depth word state) index

end
end SourceGeneratedActionWords.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
