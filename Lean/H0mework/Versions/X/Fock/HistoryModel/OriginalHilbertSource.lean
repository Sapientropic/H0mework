import H0mework.Versions.X.Fock.HistoryModel.SourceWords

/-! The actual complete-word reader is the raw source of the existing linear inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

def rawWords (depth : Nat) (current : Current) (word : List (Fock.Letter depth))
    (index : FamilyModel.Fock.Index depth) : ParentCarrier :=
  FamilyModel.Fock.reader depth index (Fock.actualWord depth word current)

theorem word_sourcePoint (depth : Nat) (word : List (Fock.Letter depth)) (current : Current) :
    run (Fock.actions depth) word (sourcePoint current) =
      sourcePoint (Fock.actualWord depth word current) := by
  induction word generalizing current with
  | nil => rfl
  | cons letter rest previous =>
      change run (Fock.actions depth) rest
          (sourceAction (Fock.step depth letter) (sourcePoint current)) =
        sourcePoint (Fock.actualWord depth rest (Fock.step depth letter current))
      rw [sourceAction_point, previous]

theorem observation_rawWords (depth : Nat) :
    SourceOwnedObservationHistory.observation (rawWords depth) =
      inventory (Fock.actions depth) (Fock.observer depth) := by
  apply Finsupp.lhom_ext'
  intro current
  apply LinearMap.ext_ring
  funext word index
  change SourceOwnedObservationHistory.observation (rawWords depth) (sourcePoint current) word index =
    Fock.observer depth (run (Fock.actions depth) word (sourcePoint current)) index
  rw [observation_point, word_sourcePoint]
  change rawWords depth current word index = SourceOwnedObservationHistory.observation
    (FamilyModel.familyRead (FamilyModel.Fock.reader depth))
    (sourcePoint (Fock.actualWord depth word current)) index
  rw [observation_point]
  rfl

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
