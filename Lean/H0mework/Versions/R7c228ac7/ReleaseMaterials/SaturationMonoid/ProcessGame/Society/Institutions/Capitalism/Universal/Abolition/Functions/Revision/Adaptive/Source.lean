import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

abbrev executable := PublicPlan.executable (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
abbrev actualState := Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit oldPast current

def inheritedWords : List (RawEvent Party Good Port Technology Instrument) :=
  match (actualState input depth count prefixLimit renewalLimit oldPast current).phase with
  | .renewal word => [word]
  | .seeking => []

def proposalWords : Compile.RawInput Party Good Port Technology Instrument →
    List (RawEvent Party Good Port Technology Instrument)
  | .code submission => [submission.requests]
  | other => PublicPlan.proposedWords other

def consumedProposals : List (RawEvent Party Good Port Technology Instrument) :=
  current.past.flatMap proposalWords

def alphabet :=
  Material.Migration.sourceAlphabet input (actualState input depth count prefixLimit renewalLimit oldPast current).raw ++
    (inheritedWords input depth count prefixLimit renewalLimit oldPast current).flatten ++
    (consumedProposals current).flatten

/-- These are fresh attempts at this exact public cut. Consumed raw syntax
supplies code candidates, never a replayed receipt or a rewritten old past. -/
def candidates :=
  inheritedWords input depth count prefixLimit renewalLimit oldPast current ++ consumedProposals current ++
    [ProgrammeSource.wordAt input (actualState input depth count prefixLimit renewalLimit oldPast current).raw] ++
    PublicFunction.words (alphabet input depth count prefixLimit renewalLimit oldPast current) (prefixLimit + renewalLimit)

abbrev Checks (word : RawEvent Party Good Port Technology Instrument) :=
  Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit oldPast current (executable word)

instance (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Checks input depth count prefixLimit renewalLimit oldPast current word) := by
  unfold Checks Macro.Public.Scope.Checks Review.Guarded.Checks
  infer_instance

#print axioms candidates

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive
