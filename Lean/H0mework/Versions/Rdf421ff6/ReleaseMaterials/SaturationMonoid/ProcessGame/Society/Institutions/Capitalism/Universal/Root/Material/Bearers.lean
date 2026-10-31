import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Material.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Participants

/-! A positive unresolved material quantity returns the receiving actor's
first original M0 birth, as well as the original instruction responsibility.
Raw stock coordinates never acquire authority by being merely named. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Material

open Source Source.Program Source.ProgrammeFace
open Financial.Installation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (state : Cursor.State input)
  (location : Party × Good) (positive : 0 < unresolved input state location)

include positive in
private theorem positive_total :
    0 < Source.Material.unresolvedTotal input.law (rawAt input state) (wordAt input state)
      (familyAt input state) (membersAt input state) location := by
  by_cases fresh : Cursor.FreshBody input state
  · simpa only [unresolved, freshAmount, if_pos fresh] using positive
  · simp [unresolved, freshAmount, fresh] at positive

theorem unresolved_item_has_actual_credit :
    0 < Decoder.acquired input.law
      (unresolvedItem input state location positive).val location.1 location.2 := by
  have atItem : 0 < Source.Material.unresolvedAmount input.law (rawAt input state)
      (wordAt input state) (familyAt input state) (membersAt input state)
      (unresolvedItem input state location positive) location :=
    (Source.Material.unresolvedOriginal input.law _ _ _ _ location
      (positive_total input state location positive)).property
  have partition := Source.Material.acquisition_partition input.law _ _
    (familyAt input state) (membersAt input state)
    (unresolvedItem input state location positive) location
  have nonnegative := Source.Material.acquisition_nonnegative input.law _ _
    (familyAt input state) (membersAt input state)
    (unresolvedItem input state location positive) location
  dsimp only [rawAt, wordAt] at atItem
  linarith [nonnegative.1, nonnegative.2.1]

def unresolvedReceiverBirth :
    ActualBirth.At input (Cursor.physicalVisit input state) location.1 :=
  (unresolvedOrigin input state location positive).participantBirth input
    (unresolvedItem input state location positive).val
    (unresolved_keeps_original_instruction input state location positive) location.1
    (Source.Material.positive_credit_has_original_recipient input.law _ location.1 location.2
      (unresolved_item_has_actual_credit input state location positive))

theorem original_receiver_and_responsibility :
    ActualBirth.lookup input (Cursor.physicalVisit input state) location.1 =
      some (unresolvedReceiverBirth input state location positive).original ∧
    (unresolvedOrigin input state location positive).instruction? input =
      some (unresolvedItem input state location positive).val :=
  ⟨(unresolvedReceiverBirth input state location positive).generated,
    unresolved_keeps_original_instruction input state location positive⟩

#print axioms unresolvedReceiverBirth
#print axioms original_receiver_and_responsibility

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Material
