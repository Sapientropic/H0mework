import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery.Access
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery.Reciprocity
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery.Disposal
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery.Evidence

/-! The finite search reads original history entries.  It never executes a
concatenated word, and its source quotations carry no completed outcome. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

private def firstSome {α β : Type} (produce : α → Option β) : List α → Option β
  | [] => none
  | head :: tail => match produce head with
    | some value => some value
    | none => firstSome produce tail

def capitalAt (access : Access input endpoint) : Option (Capital input endpoint) :=
  if access.Checks input endpoint then
    firstSome (fun evidence =>
      firstSome (fun reciprocity =>
        firstSome (fun disposal => compile input endpoint access reciprocity disposal evidence)
          (disposals input endpoint access)) (reciprocities input endpoint access))
      (evidences input endpoint access)
  else none

/-- The key is an original access ordinal and relation port.  Several later
uses of the same acquired bulk lot do not create additional access events. -/
def insert (found : List (Capital input endpoint)) (capital : Capital input endpoint) :
    List (Capital input endpoint) :=
  if found.any (fun prior => decide
    (prior.access.access.position input = capital.access.access.position input ∧
      prior.access.port = capital.access.port)) then found else found ++ [capital]

def discovered : List (Capital input endpoint) :=
  ((accesses input endpoint).filterMap (capitalAt input endpoint)).foldl (insert input endpoint) []

#print axioms capitalAt
#print axioms discovered

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery
