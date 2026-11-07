import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch.Types

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def compile : (raw : Compile.RawInput Party Good Port Technology Instrument) →
    Selection input origin members depth count prefixLimit renewalLimit current raw
  | .advance => match source : Decision.compile input origin members depth count prefixLimit renewalLimit current with
    | .action operation => .automatic operation source
    | .blocked issue => .exhausted issue source
  | .code submission =>
      if admitted : boundary input origin members depth count prefixLimit renewalLimit current then .code submission admitted
      else .codeBusy submission admitted
  | .review code =>
      if admitted : boundary input origin members depth count prefixLimit renewalLimit current then .review code admitted
      else .reviewBusy code admitted
  | .migrate pair => match Actual.Migration.inspect input origin current.raw members pair with
    | .accepted checked => .migrate pair checked
    | .refused issue => .migrationBlocked pair issue
  | .primitive request => .primitive request
  | .execute word => .execute word
  | .stopReview => .stopped

attribute [local simp] compile

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch
