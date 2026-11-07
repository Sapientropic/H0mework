import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch.Execution

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
  (control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (after : RawCurrent Party Good Technology Instrument) (accepted : Bool)

def Selection.controlAfter : {proposal : Compile.RawInput Party Good Port Technology Instrument} →
    Selection input origin members depth count prefixLimit renewalLimit current proposal →
    Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | _, .code submission _ => ⟨.seeking,submission.requests,none⟩
  | _, .review reviewCode _ => {control with review := some (ReviewCursor.initial reviewCode prefixLimit renewalLimit)}
  | _, .automatic (.repair _ attempt) _ => ⟨.seeking,attempt.tail,control.review⟩
  | _, .automatic (.migration plan _) _ =>
      if accepted then ⟨.renewal plan.pair.2,Repair.alphabet input after,none⟩ else control
  | _, .automatic (.renewal word _ _) _ =>
      if accepted then ⟨.renewal word,Repair.alphabet input after,control.review⟩ else control
  | _, .migrate pair _ =>
      if accepted then ⟨.renewal pair.2,Repair.alphabet input after,none⟩ else control
  | _, .execute _ =>
      if accepted then ⟨.seeking,Repair.alphabet input after,control.review⟩ else control
  | _, .primitive _ => {control with phase := .seeking}
  | _, _ => control

attribute [local simp] Selection.controlAfter

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch
