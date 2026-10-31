import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Macro

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {position : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {frame : Registered.Macro.NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal position}

/-- Source factory metadata does not modify the financial family, support,
source event or next. The full query root is installed only afterwards. -/
def inheritCreator (data : Registered.Macro.Continuation.FinancialData frame)
    (origin : Option (OriginAt input)) :
    Registered.Macro.Continuation.FinancialData { frame with nativeOrigin := origin } where
  Ready := data.Ready
  ready_next := data.ready_next
  bodyPaid := data.bodyPaid
  familyAt := data.familyAt
  next_support := data.next_support
  occurrence_eq_emitted := data.occurrence_eq_emitted

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Macro
