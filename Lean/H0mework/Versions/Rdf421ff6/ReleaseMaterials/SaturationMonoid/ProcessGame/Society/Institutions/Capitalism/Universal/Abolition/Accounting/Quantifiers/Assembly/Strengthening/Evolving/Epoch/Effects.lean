import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Selection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw : RawCurrent Party Good Technology Instrument} {members : List Party}
  {depth count prefixLimit renewalLimit : Nat}
  {control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
  {proposal : Compile.RawInput Party Good Port Technology Instrument}

/-- The material target is read from the actual body. This function only
updates original control coordinates after that same body's verdict. -/
def Selection.controlAfter (choice : Selection input origin raw members depth count prefixLimit renewalLimit control proposal)
    (after : RawCurrent Party Good Technology Instrument) (accepted : Bool) :
    Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  match choice with
  | .ordinary selected => selected.controlAfter control after accepted
  | .reviewing cursor _ (.fee _ _) =>
      {control with review := some {cursor with feePaid := accepted,halted := !accepted}}
  | .reviewing cursor _ (.candidate pair _ _ _) =>
      if accepted then ⟨.renewal pair.2,Repair.alphabet input after,some {cursor with renewalDue := some pair.2}⟩
      else {control with review := control.review.map (fun cursor => {cursor with halted := true})}
  | .reviewing cursor _ (.renewal word _ _) =>
      if accepted then ⟨.renewal word,Repair.alphabet input after,none⟩
      else {control with review := some {cursor with halted := true}}
  | .reviewing cursor _ (.renewalBlocked _ _ _) =>
      {control with review := some {cursor with halted := true}}
  | .reviewing cursor _ (.rejected _ tail _ _) =>
      {control with review := some {cursor with remaining := tail,feePaid := false}}
  | .reviewing cursor _ (.invalidFee _) =>
      {control with review := some {cursor with halted := true}}
  | _ => control

attribute [local simp] Selection.controlAfter

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
