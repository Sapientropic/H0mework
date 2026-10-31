import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.Boundary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

open Source.Program PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (origin : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Decision : Type
  | execute (raw : Compile.RawInput Party Good Port Technology Instrument)
  | obstructed (reason : Stop source depth count prefixLimit renewalLimit origin code)
  | released

def decideView (view : View source depth count prefixLimit renewalLimit origin code) :
    Decision source depth count prefixLimit renewalLimit origin code :=
  match view.2 with
  | .pending pending => match head : pending.remaining with
    | [] => .obstructed (.exhausted pending head)
    | _ :: _ => .execute (.primitive code.request)
  | .selected selected => .execute (.migrate selected.pair)
  | .stopped reason => .obstructed reason
  | .frontSubmitted .. => .released

theorem executing_choice_is_original_opcode
    (view : View source depth count prefixLimit renewalLimit origin code)
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (chosen : decideView source depth count prefixLimit renewalLimit origin code view = .execute raw) :
    nextRaw source depth count prefixLimit renewalLimit origin code view = some raw := by
  rcases view with ⟨current, face⟩
  cases face with
  | pending pending =>
      dsimp only [decideView] at chosen
      split at chosen
      · cases chosen
      · cases chosen
        dsimp only [nextRaw]
        simp_all
  | selected selected =>
      cases chosen
      rfl
  | stopped reason => cases chosen
  | frontSubmitted selected actual => cases chosen

namespace ContextAt

variable {source origin code}
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (context : ContextAt input)
  (current : Physical.Cursor Party Good Port Technology Instrument)

def reviewEpoch :=
  if Mandatory.FirstRenewalDue context.source.input depth count prefixLimit renewalLimit context.epoch then
    Physical.next (Physical.receive context.epoch .advance)
  else context.epoch

def dispatch : Decision context.source depth count prefixLimit renewalLimit
    (context.reviewEpoch depth count prefixLimit renewalLimit) context.fee :=
  if Mandatory.FirstRenewalDue context.source.input depth count prefixLimit renewalLimit context.epoch ∧
      current.past.length ≤ context.epoch.past.length then .execute .advance
  else decideView context.source depth count prefixLimit renewalLimit
    (context.reviewEpoch depth count prefixLimit renewalLimit) context.fee
    (atCursor context.source depth count prefixLimit renewalLimit
      (context.reviewEpoch depth count prefixLimit renewalLimit) context.fee current)

def Aligned : Prop := ReviewPhase.Aligned context.source depth count prefixLimit renewalLimit
  (context.reviewEpoch depth count prefixLimit renewalLimit) context.fee current

omit [DecidableEq Port] in
theorem registered_source_is_the_original_input : context.source.input = input := context.source_eq

end ContextAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.executing_choice_is_original_opcode
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.ContextAt.dispatch
