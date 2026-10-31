import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def previous? (current : Physical.Cursor Party Good Port Technology Instrument) :
    Option (Physical.Cursor Party Good Port Technology Instrument) :=
  if positive : 0 < current.past.length then
    some (Physical.Prefix.eventCursor current.past ⟨current.past.length - 1, by omega⟩)
  else none

def isRenewal {current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    {raw : Compile.RawInput Party Good Port Technology Instrument} :
    Compile.Result input depth count prefixLimit renewalLimit current raw → Bool
  | .accepted checked => match checked.command with
    | .automatic generated => match generated.operation with
      | .renewal .. => true
      | _ => false
    | _ => false
  | .refused _ => false

def WasRenewal {current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    {raw : Compile.RawInput Party Good Port Technology Instrument}
    (result : Compile.Result input depth count prefixLimit renewalLimit current raw) : Prop :=
  isRenewal input depth count prefixLimit renewalLimit result = true

instance {current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    {raw : Compile.RawInput Party Good Port Technology Instrument}
    (result : Compile.Result input depth count prefixLimit renewalLimit current raw) :
    Decidable (WasRenewal input depth count prefixLimit renewalLimit result) :=
  inferInstanceAs (Decidable (_ = true))

def PaidBoundary (current : Physical.Cursor Party Good Port Technology Instrument) : Prop :=
  match previous? current with
  | none => False
  | some previous => WasRenewal input depth count prefixLimit renewalLimit
      (Physical.resultAt input depth count prefixLimit renewalLimit previous)

instance (current : Physical.Cursor Party Good Port Technology Instrument) :
    Decidable (PaidBoundary input depth count prefixLimit renewalLimit current) := by
  unfold PaidBoundary
  cases previous? current <;> infer_instance

def FirstRenewalDue (current : Physical.Cursor Party Good Port Technology Instrument) : Prop :=
  match (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase with
  | .seeking => False
  | .renewal word =>
      match Review.Guarded.inspect input (Actual.origin input depth count)
          (Physical.stateAt input depth count prefixLimit renewalLimit current.past).raw (Actual.members input depth count) word with
      | .accepted _ => ¬ PaidBoundary input depth count prefixLimit renewalLimit current
      | .rejected _ => False

instance (current : Physical.Cursor Party Good Port Technology Instrument) : Decidable (FirstRenewalDue input depth count prefixLimit renewalLimit current) := by
  unfold FirstRenewalDue
  split
  · infer_instance
  · split <;> infer_instance

theorem paid_boundary_has_an_original_prefix_source
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (paid : PaidBoundary input depth count prefixLimit renewalLimit current) :
    ∃ position : Fin current.past.length, position.val + 1 = current.past.length ∧
      WasRenewal input depth count prefixLimit renewalLimit
        (Physical.resultAt input depth count prefixLimit renewalLimit (Physical.Prefix.eventCursor current.past position)) := by
  by_cases positive : 0 < current.past.length
  · let position : Fin current.past.length := ⟨current.past.length - 1, by omega⟩
    have previous : previous? current = some (Physical.Prefix.eventCursor current.past position) := by
      simp only [previous?, dif_pos positive, position]
    refine ⟨position, by dsimp [position]; omega, ?_⟩
    simpa only [PaidBoundary, previous] using paid
  · have previous : previous? current = none := by simp only [previous?, dif_neg positive]
    simp only [PaidBoundary, previous] at paid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory
