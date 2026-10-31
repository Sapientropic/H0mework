import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)

/-- A native state is read from this creator and this consumed prefix.
The constructor is sealed so the source cannot receive a completed GS. -/
structure RecordedAt where
  private mk ::
  origin : OriginAt input
  state : (index : origin.Slot) → (origin.process depth count).GeneratedState
  generated : ∀ index, state index = origin.state depth count
    (atPast origin depth count prefixLimit renewalLimit snapshot.past index)

inductive ReadoutAt
  | undisclosed
  | recorded (scope : RecordedAt input depth count prefixLimit renewalLimit snapshot)

def readout (origin : Option (OriginAt input)) :
    ReadoutAt input depth count prefixLimit renewalLimit snapshot :=
  match origin with
  | none => .undisclosed
  | some creator => .recorded ⟨creator,
      fun index => creator.state depth count (atPast creator depth count prefixLimit renewalLimit snapshot.past index),
      fun _ => rfl⟩

def OriginalScopePaid : ReadoutAt input depth count prefixLimit renewalLimit snapshot → Prop
  | .undisclosed => False
  | .recorded scope => ∀ index, (scope.state index).current.TerminalAt 0

theorem undisclosed_does_not_certify_the_original_scope :
    ¬ OriginalScopePaid input depth count prefixLimit renewalLimit snapshot .undisclosed := id

theorem an_undisclosed_origin_is_not_a_native_completion :
    readout input depth count prefixLimit renewalLimit snapshot none = .undisclosed := rfl

theorem a_declared_origin_reads_the_original_complete_state (origin : OriginAt input) :
    ∃ scope, readout input depth count prefixLimit renewalLimit snapshot (some origin) = .recorded scope ∧
      scope.origin = origin ∧
      ∀ index, scope.state index = scope.origin.state depth count
        (atPast scope.origin depth count prefixLimit renewalLimit snapshot.past index) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

#print axioms a_declared_origin_reads_the_original_complete_state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
