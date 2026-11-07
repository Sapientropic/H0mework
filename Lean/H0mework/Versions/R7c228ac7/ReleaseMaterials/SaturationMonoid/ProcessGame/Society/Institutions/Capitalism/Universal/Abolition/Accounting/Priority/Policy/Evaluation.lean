import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Rules

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party)

inductive AcceptedPrefix : RawEvent Party Good Port Technology Instrument → Prop
  | nil : AcceptedPrefix []
  | snoc (front : RawEvent Party Good Port Technology Instrument) (request : Request Party Good Port Technology Instrument)
      (earlier : AcceptedPrefix front)
      (declared : state.declared = true) (standing : known members request)
      (material : Responsibility.Family.materialOperation (Responsibility.controllerCohort source past nature response)
        (Responsibility.Family.positiveScope source past nature response) request)
      (valid : law.Valid (current claim state law front) request)
      (amount : amountAllowed claim state law members front request)
      (control : preservesControl claim state law members front request) : AcceptedPrefix (front ++ [request])

structure StoppedAt (proposal : RawEvent Party Good Port Technology Instrument) : Type where
  front : RawEvent Party Good Port Technology Instrument
  request : Request Party Good Port Technology Instrument
  suffix : RawEvent Party Good Port Technology Instrument
  original : proposal = front ++ request :: suffix
  denied : Denial claim state law members front request

/-- The original proposal is never rewritten as a success: its first denied
request and original suffix remain source data beside the executed front. -/
structure Evaluation (proposal : RawEvent Party Good Port Technology Instrument) : Type where
  executableWord : RawEvent Party Good Port Technology Instrument
  remainder : RawEvent Party Good Port Technology Instrument
  original : proposal = executableWord ++ remainder
  stop : Option (StoppedAt claim state law members proposal)
  accepted : AcceptedPrefix claim state law members executableWord
  complete_when_noStop : stop = none → remainder = []
  stoppedMatches : ∀ issue, stop = some issue → issue.front = executableWord ∧ remainder = issue.request :: issue.suffix

private def scanFrom (front : RawEvent Party Good Port Technology Instrument)
    (accepted : AcceptedPrefix claim state law members front) :
    (remaining : RawEvent Party Good Port Technology Instrument) →
      Evaluation claim state law members (front ++ remaining)
  | [] => ⟨front,[],rfl,none,accepted,(fun _ => rfl),(by intro issue impossible; cases impossible)⟩
  | request :: suffix =>
    match decideRequest claim state law members front request with
    | .permitted declared standing material valid amount control => by
        have later := scanFrom (front ++ [request])
          (.snoc front request accepted declared standing material valid amount control) suffix
        simpa only [List.append_assoc,List.singleton_append] using later
    | .denied issue => by
        let halted : StoppedAt claim state law members (front ++ request :: suffix) :=
          ⟨front,request,suffix,rfl,issue⟩
        exact ⟨front,request :: suffix,rfl,some halted,accepted,
          (by intro impossible; cases impossible),
          (by intro found same; cases Option.some.inj same; exact ⟨rfl,rfl⟩)⟩

def evaluate (proposal : RawEvent Party Good Port Technology Instrument) :
    Evaluation claim state law members proposal := by
  simpa only [List.nil_append] using scanFrom claim state law members [] .nil proposal

namespace Evaluation
variable {claim state law members} {proposal : RawEvent Party Good Port Technology Instrument}

def updated (evaluation : Evaluation claim state law members proposal) : Responsibility.Family.State claim :=
  Responsibility.Family.State.advance claim state law evaluation.executableWord

def actualWord (evaluation : Evaluation claim state law members proposal) : RawEvent Party Good Port Technology Instrument :=
  (Responsibility.Family.State.attempt claim state law evaluation.executableWord).actualWord

end Evaluation
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy
