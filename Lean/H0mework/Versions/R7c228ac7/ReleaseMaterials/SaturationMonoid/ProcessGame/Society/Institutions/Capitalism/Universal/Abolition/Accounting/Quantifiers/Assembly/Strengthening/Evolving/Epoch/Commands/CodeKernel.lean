import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.CodeKernel

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)
  (control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (submission : Actual.Submission Party Good Port Technology Instrument)
  (unregistered : control.review = none)
  (admitted : boundary input origin members depth count prefixLimit renewalLimit (control.atRaw raw))

include unregistered admitted in
theorem executionRaw :
    (select input origin raw members depth count prefixLimit renewalLimit control (.code submission)).executionRaw = .code submission := by
  cases control with
  | mk phase remaining review =>
      cases review with
      | none =>
          simp only [select,Dispatch.compile,dif_pos admitted,Selection.executionRaw,Dispatch.Selection.executionRaw]
      | some => cases unregistered

include unregistered admitted in
theorem controlAfter (after : RawCurrent Party Good Technology Instrument) (accepted : Bool) :
    (select input origin raw members depth count prefixLimit renewalLimit control (.code submission)).controlAfter after accepted =
      ⟨.seeking,submission.requests,none⟩ := by
  cases control with
  | mk phase remaining review =>
      cases review with
      | none =>
          simp only [select,Dispatch.compile,dif_pos admitted,Selection.controlAfter,Dispatch.Selection.controlAfter]
      | some => cases unregistered

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.CodeKernel
