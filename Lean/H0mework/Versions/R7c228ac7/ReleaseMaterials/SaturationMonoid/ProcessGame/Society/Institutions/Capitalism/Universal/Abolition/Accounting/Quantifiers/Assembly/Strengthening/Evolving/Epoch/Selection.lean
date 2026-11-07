import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch.Execution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Review.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)
  (control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (proposal : Compile.RawInput Party Good Port Technology Instrument)

inductive Selection : Type
  | ordinary (choice : Dispatch.Selection input origin members depth count prefixLimit renewalLimit (control.atRaw raw) proposal)
  | reviewing (cursor : ReviewCursor (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
      (source : control.review = some cursor) (choice : Review.Selection input origin raw members cursor)

def select : Selection input origin raw members depth count prefixLimit renewalLimit control proposal :=
  match source : control.review with
  | none => .ordinary (Dispatch.compile input origin members depth count prefixLimit renewalLimit (control.atRaw raw) proposal)
  | some cursor =>
      if cursor.recourse then
        .ordinary (Dispatch.compile input origin members depth count prefixLimit renewalLimit (control.atRaw raw) proposal)
      else .reviewing cursor source (Review.compile input origin raw members cursor)

namespace Selection
variable {input origin raw members depth count prefixLimit renewalLimit control proposal}

def executionRaw : Selection input origin raw members depth count prefixLimit renewalLimit control proposal →
    Compile.RawInput Party Good Port Technology Instrument
  | .ordinary choice => choice.executionRaw
  | .reviewing _ _ choice => choice.executionRaw

end Selection
-- Shared equation theorems are generated in their defining module.
attribute [local simp] select Selection.executionRaw

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
