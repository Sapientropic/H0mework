import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument} {members : List Party}
  {depth count prefixLimit renewalLimit : Nat}
  {current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}

def Selection.executionRaw : {proposal : Compile.RawInput Party Good Port Technology Instrument} →
    Selection input origin members depth count prefixLimit renewalLimit current proposal →
    Compile.RawInput Party Good Port Technology Instrument
  | _, .automatic operation _ => match operation with
    | .migration plan _ => .execute plan.pair.1
    | .renewal word _ _ => .execute word
    | .repair _ attempt => .primitive attempt.request
  | _, .code submission _ => .code submission
  | _, .review reviewCode _ => .review reviewCode
  | _, .migrate pair _ => .execute pair.1
  | _, .primitive request => .primitive request
  | _, .execute word => .execute word
  | _, _ => .stopReview

attribute [local simp] Selection.executionRaw

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch
