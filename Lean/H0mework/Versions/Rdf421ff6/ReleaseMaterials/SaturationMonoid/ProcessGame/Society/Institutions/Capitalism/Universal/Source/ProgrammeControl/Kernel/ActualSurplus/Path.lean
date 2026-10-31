import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Routes

/-! Material transport never transfers a control right.  A change of good
is admitted only at a real production leg controlled by the same source
port.  Every item retains its original before-current and permissions. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- This raw leg predicate also serves a history carrier: it has no word
or local-index premise.  The caller keeps the original chronological order. -/
def flowLegAllowed (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (recipient : Party) (fromCell toCell : Party × Good) : Prop :=
  law.Valid item.before item.request ∧
  0 < flowAt (law.actualDebit item.before item.request) fromCell.1 fromCell.2 ∧
  0 < flowAt (law.actualCredit item.before item.request) toCell.1 toCell.2 ∧
  match item.request.operation with
  | .produce _ => port ∈ law.requiredPorts item.before item.request ∧
      PrivatePhase law item.before port recipient
  | .transfer .. | .settle .. => fromCell.2 = toCell.2
  | _ => False

instance (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (recipient : Party) (fromCell toCell : Party × Good) :
    Decidable (flowLegAllowed law item port recipient fromCell toCell) := by
  unfold flowLegAllowed
  cases item.request.operation <;> infer_instance

variable (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument) (port : Port) (recipient : Party)

def controlAlong : Party × Good → List (RouteLeg law current word) → Prop
  | _, [] => True
  | source, leg :: tail => flowLegAllowed law leg.item.val port recipient source leg.destination ∧
      controlAlong leg.destination tail

instance (source : Party × Good) (route : List (RouteLeg law current word)) :
    Decidable (controlAlong law current word port recipient source route) := by
  induction route generalizing source with
  | nil => unfold controlAlong; infer_instance
  | cons head tail prior =>
      unfold controlAlong
      letI := prior head.destination
      infer_instance

private def extend (item : OriginalItem law current word)
    (routes : Discovery.Routes law current word) : Discovery.Routes law current word :=
  routes.foldl (fun found prior =>
    (law.actualCredit item.val.before item.val.request).foldl (fun result lot =>
      if flowLegAllowed law item.val port recipient prior.1 lot.1 then
        Discovery.insertRoute law current word result lot.1 (prior.2 ++ [⟨item, lot.1⟩])
      else result) found) routes

def controlledRouteBetween (origin target : Party × Good) (lower upper : Nat) :
    Option (List (RouteLeg law current word)) :=
  Discovery.findRoute law current word
    ((law.rawItems current word).attach.foldl (fun routes item =>
      if lower ≤ item.val.index ∧ item.val.index < upper then
        extend law current word port recipient item routes else routes) [(origin, [])]) target

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus
